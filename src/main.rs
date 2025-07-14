// Tested with nightly-2025-03-28

#![feature(rustc_private)]

// extern crate do_not_use_safe_print;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_expand;
extern crate rustc_feature;
extern crate rustc_fluent_macro;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_parse;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate serde_json;
extern crate tracing;

// use rustc_fluent_macro::fluent_generated;

use rustc_errors::registry;
use rustc_hash::FxHashMap;
use rustc_session::config;

use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{self, IsTerminal, Read, Write};
use std::panic::{self, PanicHookInfo, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::{self, Command, Stdio};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use std::{env, str};

use rustc_ast as ast;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenErrors, CodegenResults};
use rustc_data_structures::profiling::{
    TimePassesFormat, get_resident_set_size, print_time_passes_entry,
};
use rustc_errors::emitter::stderr_destination;
use rustc_errors::registry::Registry;
use rustc_errors::translation::Translator;
use rustc_errors::{ColorConfig, DiagCtxt, ErrCode, FatalError, PResult, markdown};
use rustc_feature::find_gated_cfg;
// This avoids a false positive with `-Wunused_crate_dependencies`.
// `rust_index` isn't used in this crate's code, but it must be named in the
// `Cargo.toml` for the `rustc_randomized_layouts` feature.
use rustc_index as _;
use rustc_interface::util::{self, get_codegen_backend};
use rustc_interface::{Linker, create_and_enter_global_ctxt, interface, passes};
use rustc_lint::unerased_lint_store;
use rustc_metadata::creader::MetadataLoader;
use rustc_metadata::locator;
use rustc_middle::ty::TyCtxt;
use rustc_parse::{new_parser_from_file, new_parser_from_source_str, unwrap_or_emit_fatal};
use rustc_session::config::{
    CG_OPTIONS, CrateType, ErrorOutputType, Input, OptionDesc, OutFileName, OutputType, Sysroot,
    UnstableOptions, Z_OPTIONS, nightly_options, parse_target_triple,
};
use rustc_session::getopts::{self, Matches};
use rustc_session::lint::{Lint, LintId};
use rustc_session::output::{CRATE_TYPES, collect_crate_types, invalid_output_for_target};
use rustc_session::{EarlyDiagCtxt, Session}; // config
use rustc_span::FileName;
use rustc_span::def_id::LOCAL_CRATE;
use rustc_target::json::ToJson;
use rustc_target::spec::{Target, TargetTuple};
use tracing::trace;

/* This module cannot be included because of missing dependencies */
// mod session_diagnostics;
// use crate::session_diagnostics::{
//     CantEmitMIR, RLinkEmptyVersionNumber, RLinkEncodingVersionMismatch, RLinkRustcVersionMismatch,
//     RLinkWrongFileType, RlinkCorruptFile, RlinkNotAFile, RlinkUnableToRead, UnstableFeatureUsage,
// };

fn main() {
    let args: Vec<String> = std::env::args().collect();

    run_compiler(&args);
}

fn run_compiler(at_args: &[String]) {
    let mut default_early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());

    let at_args = at_args.get(1..).unwrap_or_default();

    let args = rustc_driver::args::arg_expand_all(&default_early_dcx, at_args);

    let Some(matches) = rustc_driver::handle_options(&default_early_dcx, &args) else {
        return;
    };

    let sopts = rustc_session::config::build_session_options(&mut default_early_dcx, &matches);

    /* No ice file */
    // let ice_file = ice_path_with_config(Some(&sopts.unstable_opts)).clone();

    /* Not sure what this does */
    // if let Some(ref code) = matches.opt_str("explain") {
    //     handle_explain(&default_early_dcx, diagnostics_registry(), code, sopts.color);
    //     return;
    // }

    let input = make_input(&default_early_dcx, &matches.free);
    let has_input = input.is_some();
    let (odir, ofile) = make_output(&matches);

    drop(default_early_dcx);

    let mut config = rustc_interface::Config {
        opts: sopts,
        crate_cfg: matches.opt_strs("cfg"),
        crate_check_cfg: matches.opt_strs("check-cfg"),
        input: input.unwrap_or(rustc_session::config::Input::File(std::path::PathBuf::new())),
        output_file: ofile,
        output_dir: odir,
        file_loader: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_owned(),
        lint_caps: Default::default(),
        psess_created: None,
        hash_untracked_state: None,
        register_lints: None,
        override_queries: None,
        extra_symbols: Vec::new(),
        make_codegen_backend: None,
        ice_file: None,
        registry: diagnostics_registry(),
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
        expanded_args: args,
    };

    /* No callbacks supported yet, unlikely the average crate uses callbacks */
    // callbacks.config(&mut config);

    let registered_lints = config.register_lints.is_some();

    rustc_interface::run_compiler(config, |compiler| {
        let sess = &compiler.sess;
        let codegen_backend = &*compiler.codegen_backend;

        // This is used for early exits unrelated to errors. E.g. when just
        // printing some information without compiling, or exiting immediately
        // after parsing, etc.
        let early_exit = || {
            sess.dcx().abort_if_errors();
        };

        // This implements `-Whelp`. It should be handled very early, like
        // `--help`/`-Zhelp`/`-Chelp`. This is the earliest it can run, because
        // it must happen after lints are registered, during session creation.
        if sess.opts.describe_lints {
            describe_lints(sess, registered_lints);
            return early_exit();
        }

        /* needed to compile basic crates because cargo requests version and other information from rustc */
        if print_crate_info(codegen_backend, sess, has_input) == rustc_driver::Compilation::Stop {
            return early_exit();
        }

        if !has_input {
            #[allow(rustc::diagnostic_outside_of_impl)]
            sess.dcx().fatal("no input filename given"); // this is fatal
        }

        if !sess.opts.unstable_opts.ls.is_empty() {
            list_metadata(sess, &*codegen_backend.metadata_loader());
            return early_exit();
        }

        /* what is process_rlink? blocked because can't find something needed for #![derive(Diagnostics)] in session_diagnostics.rs */
        if sess.opts.unstable_opts.link_only {
            // process_rlink(sess, compiler);
            return early_exit();
        }

        // Parse the crate root source code (doesn't parse submodules yet)
        // Everything else is parsed during macro expansion.
        let mut krate = rustc_interface::passes::parse(sess);

        /* Do some manipulations? Need to verify what krate could be missing, e.g., other files/modules */

        // If pretty printing is requested: Figure out the representation, print it and exit
        if let Some(pp_mode) = sess.opts.pretty {
            if pp_mode.needs_ast_map() {
                rustc_interface::create_and_enter_global_ctxt(compiler, krate, |tcx| {
                    tcx.ensure_ok().early_lint_checks(());
                    rustc_driver::pretty::print(
                        sess,
                        pp_mode,
                        rustc_driver::pretty::PrintExtra::NeedsAstMap { tcx },
                    );
                    rustc_interface::passes::write_dep_info(tcx);
                });
            } else {
                rustc_driver::pretty::print(
                    sess,
                    pp_mode,
                    rustc_driver::pretty::PrintExtra::AfterParsing { krate: &krate },
                );
            }
            // trace!("finished pretty-printing");
            return early_exit();
        }

        /* No callbacks */
        // if callbacks.after_crate_root_parsing(compiler, &mut krate) == Compilation::Stop {
        //     return early_exit();
        // }

        if sess.opts.unstable_opts.parse_crate_root_only {
            return early_exit();
        }

        let linker = rustc_interface::create_and_enter_global_ctxt(compiler, krate, |tcx| {
            let early_exit = || {
                sess.dcx().abort_if_errors();
                None
            };

            // Make sure name resolution and macro expansion is run.
            let _ = tcx.resolver_for_lowering();

            /* No callbacks */
            // if callbacks.after_expansion(compiler, tcx) == Compilation::Stop {
            //     return early_exit();
            // }

            rustc_interface::passes::write_dep_info(tcx);

            rustc_interface::passes::write_interface(tcx);

            if sess
                .opts
                .output_types
                .contains_key(&rustc_session::config::OutputType::DepInfo)
                && sess.opts.output_types.len() == 1
            {
                return early_exit();
            }

            if sess.opts.unstable_opts.no_analysis {
                return early_exit();
            }

            tcx.ensure_ok().analysis(());

            /* No metrics */
            // if let Some(metrics_dir) = &sess.opts.unstable_opts.metrics_dir {
            //     dump_feature_usage_metrics(tcx, metrics_dir);
            // }

            /* No callbacks */
            // if callbacks.after_analysis(compiler, tcx) == Compilation::Stop {
            //     return early_exit();
            // }

            /* No diagnostics */
            // if tcx
            //     .sess
            //     .opts
            //     .output_types
            //     .contains_key(&rustc_session::config::OutputType::Mir)
            // {
            //     if let Err(error) = rustc_mir_transform::dump_mir::emit_mir(tcx) {
            //         tcx.dcx().emit_fatal(CantEmitMIR { error });
            //     }
            // }

            Some(rustc_interface::Linker::codegen_and_build_linker(
                tcx,
                &*compiler.codegen_backend,
            ))
        });

        // Linking is done outside the `compiler.enter()` so that the
        // `GlobalCtxt` within `Queries` can be freed as early as possible.
        if let Some(linker) = linker {
            linker.link(sess, codegen_backend);
        }

        println!("done.");
    })
}

/* Cannot include these functions for diagnostics (or linking?) due to missing dependencies */
// fn process_rlink(sess: &Session, compiler: &interface::Compiler) {
//     assert!(sess.opts.unstable_opts.link_only);
//     let dcx = sess.dcx();
//     if let Input::File(file) = &sess.io.input {
//         let rlink_data = fs::read(file).unwrap_or_else(|err| {
//             dcx.emit_fatal(RlinkUnableToRead { err });
//         });
//         let (codegen_results, metadata, outputs) =
//             match CodegenResults::deserialize_rlink(sess, rlink_data) {
//                 Ok((codegen, metadata, outputs)) => (codegen, metadata, outputs),
//                 Err(err) => {
//                     match err {
//                         CodegenErrors::WrongFileType => dcx.emit_fatal(RLinkWrongFileType),
//                         CodegenErrors::EmptyVersionNumber => {
//                             dcx.emit_fatal(RLinkEmptyVersionNumber)
//                         }
//                         CodegenErrors::EncodingVersionMismatch { version_array, rlink_version } => {
//                             dcx.emit_fatal(RLinkEncodingVersionMismatch {
//                                 version_array,
//                                 rlink_version,
//                             })
//                         }
//                         CodegenErrors::RustcVersionMismatch { rustc_version } => {
//                             dcx.emit_fatal(RLinkRustcVersionMismatch {
//                                 rustc_version,
//                                 current_version: sess.cfg_version,
//                             })
//                         }
//                         CodegenErrors::CorruptFile => {
//                             dcx.emit_fatal(RlinkCorruptFile { file });
//                         }
//                     };
//                 }
//             };
//         compiler.codegen_backend.link(sess, codegen_results, metadata, &outputs);
//     } else {
//         dcx.emit_fatal(RlinkNotAFile {});
//     }
// }

// fn dump_feature_usage_metrics(tcxt: TyCtxt<'_>, metrics_dir: &Path) {
//     let hash = tcxt.crate_hash(LOCAL_CRATE);
//     let crate_name = tcxt.crate_name(LOCAL_CRATE);
//     let metrics_file_name = format!("unstable_feature_usage_metrics-{crate_name}-{hash}.json");
//     let metrics_path = metrics_dir.join(metrics_file_name);
//     if let Err(error) = tcxt.features().dump_feature_usage_metrics(metrics_path) {
//         // FIXME(yaahc): once metrics can be enabled by default we will want "failure to emit
//         // default metrics" to only produce a warning when metrics are enabled by default and emit
//         // an error only when the user manually enables metrics
//         tcxt.dcx().emit_err(UnstableFeatureUsage { error });
//     }
// }

fn list_metadata(sess: &Session, metadata_loader: &dyn MetadataLoader) {
    match sess.io.input {
        Input::File(ref ifile) => {
            let path = &(*ifile);
            let mut v = Vec::new();
            locator::list_file_metadata(
                &sess.target,
                path,
                metadata_loader,
                &mut v,
                &sess.opts.unstable_opts.ls,
                sess.cfg_version,
            )
            .unwrap();
            println!("{}", String::from_utf8(v).unwrap());
        }
        Input::Str { .. } => {
            #[allow(rustc::diagnostic_outside_of_impl)]
            sess.dcx().fatal("cannot list metadata for stdin");
        }
    }
}

fn parse_crate_attrs<'a>(sess: &'a Session) -> PResult<'a, ast::AttrVec> {
    let mut parser = unwrap_or_emit_fatal(match &sess.io.input {
        Input::File(file) => new_parser_from_file(&sess.psess, file, None),
        Input::Str { name, input } => {
            new_parser_from_source_str(&sess.psess, name.clone(), input.clone())
        }
    });
    parser.parse_inner_attributes()
}

fn print_crate_info(
    codegen_backend: &dyn CodegenBackend,
    sess: &Session,
    parse_attrs: bool,
) -> rustc_driver::Compilation {
    use rustc_session::config::PrintKind::*;
    // This import prevents the following code from using the printing macros
    // used by the rest of the module. Within this function, we only write to
    // the output specified by `sess.io.output_file`.
    // #[allow(unused_imports)]
    // use {do_not_use_safe_print as safe_print, do_not_use_safe_print as safe_println};

    // NativeStaticLibs and LinkArgs are special - printed during linking
    // (empty iterator returns true)
    if sess
        .opts
        .prints
        .iter()
        .all(|p| p.kind == NativeStaticLibs || p.kind == LinkArgs)
    {
        return rustc_driver::Compilation::Continue;
    }

    let attrs = if parse_attrs {
        let result = parse_crate_attrs(sess);
        match result {
            Ok(attrs) => Some(attrs),
            Err(parse_error) => {
                parse_error.emit();
                return rustc_driver::Compilation::Stop;
            }
        }
    } else {
        None
    };

    for req in &sess.opts.prints {
        let mut crate_info = String::new();
        // macro println_info($($arg:tt)*) {
        //     crate_info.write_fmt(format_args!("{}\n", format_args!($($arg)*))).unwrap()
        // }

        match req.kind {
            TargetList => {
                let mut targets = rustc_target::spec::TARGETS.to_vec();
                targets.sort_unstable();
                println!("{}", targets.join("\n"));
            }
            HostTuple => println!("{}", rustc_session::config::host_tuple()),
            Sysroot => println!("{}", sess.opts.sysroot.path().display()),
            TargetLibdir => println!("{}", sess.target_tlib_path.dir.display()),
            TargetSpecJson => {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&sess.target.to_json()).unwrap()
                );
            }
            AllTargetSpecsJson => {
                let mut targets = BTreeMap::new();
                for name in rustc_target::spec::TARGETS {
                    let triple = TargetTuple::from_tuple(name);
                    let target = Target::expect_builtin(&triple);
                    targets.insert(name, target.to_json());
                }
                println!("{}", serde_json::to_string_pretty(&targets).unwrap());
            }
            FileNames => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return rustc_driver::Compilation::Continue;
                };
                let t_outputs = rustc_interface::util::build_output_filenames(attrs, sess);
                let crate_name = passes::get_crate_name(sess, attrs);
                let crate_types = collect_crate_types(sess, attrs);
                for &style in &crate_types {
                    let fname = rustc_session::output::filename_for_input(
                        sess, style, crate_name, &t_outputs,
                    );
                    println!("{}", fname.as_path().file_name().unwrap().to_string_lossy());
                }
            }
            CrateName => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return rustc_driver::Compilation::Continue;
                };
                println!("{}", passes::get_crate_name(sess, attrs));
            }
            CrateRootLintLevels => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return rustc_driver::Compilation::Continue;
                };
                let crate_name = passes::get_crate_name(sess, attrs);
                let lint_store = crate::unerased_lint_store(sess);
                let registered_tools = rustc_resolve::registered_tools_ast(sess.dcx(), attrs);
                let features = rustc_expand::config::features(sess, attrs, crate_name);
                let lint_levels = rustc_lint::LintLevelsBuilder::crate_root(
                    sess,
                    &features,
                    true,
                    lint_store,
                    &registered_tools,
                    attrs,
                );
                for lint in lint_store.get_lints() {
                    if let Some(feature_symbol) = lint.feature_gate
                        && !features.enabled(feature_symbol)
                    {
                        // lint is unstable and feature gate isn't active, don't print
                        continue;
                    }
                    let level = lint_levels.lint_level(lint).level;
                    println!("{}={}", lint.name_lower(), level.as_str());
                }
            }
            Cfg => {
                let mut cfgs = sess
                    .psess
                    .config
                    .iter()
                    .filter_map(|&(name, value)| {
                        // On stable, exclude unstable flags.
                        if !sess.is_nightly_build()
                            && find_gated_cfg(|cfg_sym| cfg_sym == name).is_some()
                        {
                            return None;
                        }

                        if let Some(value) = value {
                            Some(format!("{name}=\"{value}\""))
                        } else {
                            Some(name.to_string())
                        }
                    })
                    .collect::<Vec<String>>();

                cfgs.sort();
                for cfg in cfgs {
                    println!("{cfg}");
                }
            }
            CheckCfg => {
                let mut check_cfgs: Vec<String> = Vec::with_capacity(410);

                // INSTABILITY: We are sorting the output below.
                #[allow(rustc::potential_query_instability)]
                for (name, expected_values) in &sess.psess.check_config.expecteds {
                    use crate::config::ExpectedValues;
                    match expected_values {
                        ExpectedValues::Any => check_cfgs.push(format!("{name}=any()")),
                        ExpectedValues::Some(values) => {
                            if !values.is_empty() {
                                check_cfgs.extend(values.iter().map(|value| {
                                    if let Some(value) = value {
                                        format!("{name}=\"{value}\"")
                                    } else {
                                        name.to_string()
                                    }
                                }))
                            } else {
                                check_cfgs.push(format!("{name}="))
                            }
                        }
                    }
                }

                check_cfgs.sort_unstable();
                if !sess.psess.check_config.exhaustive_names {
                    if !sess.psess.check_config.exhaustive_values {
                        println!("any()=any()");
                    } else {
                        println!("any()");
                    }
                }
                for check_cfg in check_cfgs {
                    println!("{check_cfg}");
                }
            }
            CallingConventions => {
                let calling_conventions = rustc_abi::all_names();
                println!("{}", calling_conventions.join("\n"));
            }
            RelocationModels
            | CodeModels
            | TlsModels
            | TargetCPUs
            | StackProtectorStrategies
            | TargetFeatures => {
                codegen_backend.print(req, &mut crate_info, sess);
            }
            // Any output here interferes with Cargo's parsing of other printed output
            NativeStaticLibs => {}
            LinkArgs => {}
            SplitDebuginfo => {
                use rustc_target::spec::SplitDebuginfo::{Off, Packed, Unpacked};

                for split in &[Off, Packed, Unpacked] {
                    if sess
                        .target
                        .options
                        .supported_split_debuginfo
                        .contains(split)
                    {
                        println!("{split}");
                    }
                }
            }
            DeploymentTarget => {
                if sess.target.is_like_darwin {
                    println!(
                        "{}={}",
                        rustc_target::spec::apple::deployment_target_env_var(&sess.target.os),
                        sess.apple_deployment_target().fmt_pretty(),
                    )
                } else {
                    #[allow(rustc::diagnostic_outside_of_impl)]
                    sess.dcx()
                        .fatal("only Apple targets currently support deployment version info")
                }
            }
            SupportedCrateTypes => {
                let supported_crate_types = CRATE_TYPES
                    .iter()
                    .filter(|(_, crate_type)| !invalid_output_for_target(&sess, *crate_type))
                    .filter(|(_, crate_type)| *crate_type != CrateType::Sdylib)
                    .map(|(crate_type_sym, _)| *crate_type_sym)
                    .collect::<BTreeSet<_>>();
                for supported_crate_type in supported_crate_types {
                    println!("{}", supported_crate_type.as_str());
                }
            }
        }

        req.out.overwrite(&crate_info, sess);
    }
    rustc_driver::Compilation::Stop
}

pub fn describe_lints(sess: &rustc_session::Session, registered_lints: bool) {
    println!(
        "
Available lint options:
    -W <foo>           Warn about <foo>
    -A <foo>           Allow <foo>
    -D <foo>           Deny <foo>
    -F <foo>           Forbid <foo> (deny <foo> and all attempts to override)

"
    );

    fn sort_lints(
        sess: &rustc_session::Session,
        mut lints: Vec<&'static rustc_lint::Lint>,
    ) -> Vec<&'static rustc_lint::Lint> {
        // The sort doesn't case-fold but it's doubtful we care.
        lints.sort_by_cached_key(|x: &&rustc_lint::Lint| (x.default_level(sess.edition()), x.name));
        lints
    }

    fn sort_lint_groups(
        lints: Vec<(&'static str, Vec<rustc_lint::LintId>, bool)>,
    ) -> Vec<(&'static str, Vec<rustc_lint::LintId>)> {
        let mut lints: Vec<_> = lints.into_iter().map(|(x, y, _)| (x, y)).collect();
        lints.sort_by_key(|l| l.0);
        lints
    }

    let lint_store = rustc_lint::unerased_lint_store(sess);
    let (loaded, builtin): (Vec<_>, _) = lint_store
        .get_lints()
        .iter()
        .cloned()
        .partition(|&lint| lint.is_externally_loaded);
    let loaded = sort_lints(sess, loaded);
    let builtin = sort_lints(sess, builtin);

    let (loaded_groups, builtin_groups): (Vec<_>, _) =
        lint_store.get_lint_groups().partition(|&(.., p)| p);
    let loaded_groups = sort_lint_groups(loaded_groups);
    let builtin_groups = sort_lint_groups(builtin_groups);

    let max_name_len = loaded
        .iter()
        .chain(&builtin)
        .map(|&s| s.name.chars().count())
        .max()
        .unwrap_or(0);
    let padded = |x: &str| {
        let mut s = " ".repeat(max_name_len - x.chars().count());
        s.push_str(x);
        s
    };

    println!("rustc_lint::Lint checks provided by rustc:\n");

    let print_lints = |lints: Vec<&rustc_lint::Lint>| {
        println!("    {}  {:7.7}  {}", padded("name"), "default", "meaning");
        println!("    {}  {:7.7}  {}", padded("----"), "-------", "-------");
        for lint in lints {
            let name = lint.name_lower().replace('_', "-");
            println!(
                "    {}  {:7.7}  {}",
                padded(&name),
                lint.default_level(sess.edition()).as_str(),
                lint.desc
            );
        }
        println!("\n");
    };

    print_lints(builtin);

    let max_name_len = std::cmp::max(
        "warnings".len(),
        loaded_groups
            .iter()
            .chain(&builtin_groups)
            .map(|&(s, _)| s.chars().count())
            .max()
            .unwrap_or(0),
    );

    let padded = |x: &str| {
        let mut s = " ".repeat(max_name_len - x.chars().count());
        s.push_str(x);
        s
    };

    println!("Lint groups provided by rustc:\n");

    let print_lint_groups = |lints: Vec<(&'static str, Vec<rustc_lint::LintId>)>, all_warnings| {
        println!("    {}  sub-lints", padded("name"));
        println!("    {}  ---------", padded("----"));

        if all_warnings {
            println!(
                "    {}  all lints that are set to issue warnings",
                padded("warnings")
            );
        }

        for (name, to) in lints {
            let name = name.to_lowercase().replace('_', "-");
            let desc = to
                .into_iter()
                .map(|x| x.to_string().replace('_', "-"))
                .collect::<Vec<String>>()
                .join(", ");
            println!("    {}  {}", padded(&name), desc);
        }
        println!("\n");
    };

    print_lint_groups(builtin_groups, true);

    match (registered_lints, loaded.len(), loaded_groups.len()) {
        (false, 0, _) | (false, _, 0) => {
            println!("Lint tools like Clippy can load additional lints and lint groups.");
        }
        (false, ..) => panic!("didn't load additional lints but got them anyway!"),
        (true, 0, 0) => {
            println!("This crate does not load any additional lints or lint groups.")
        }
        (true, l, g) => {
            if l > 0 {
                println!("Lint checks loaded by this crate:\n");
                print_lints(loaded);
            }
            if g > 0 {
                println!("Lint groups loaded by this crate:\n");
                print_lint_groups(loaded_groups, false);
            }
        }
    }
}

fn make_input(
    early_dcx: &rustc_session::EarlyDiagCtxt,
    free_matches: &[String],
) -> Option<rustc_session::config::Input> {
    match free_matches {
        [] => None, // no input: we will exit early,
        [ifile] if ifile == "-" => {
            // read from stdin as `Input::Str`
            let mut input = String::new();
            if std::io::stdin().read_to_string(&mut input).is_err() {
                // Immediately stop compilation if there was an issue reading
                // the input (for example if the input stream is not UTF-8).
                early_dcx
                    .early_fatal("couldn't read from stdin, as it did not contain valid UTF-8");
            }

            let name = match std::env::var("UNSTABLE_RUSTDOC_TEST_PATH") {
                Ok(path) => {
                    let line = std::env::var("UNSTABLE_RUSTDOC_TEST_LINE").expect(
                        "when UNSTABLE_RUSTDOC_TEST_PATH is set \
                                    UNSTABLE_RUSTDOC_TEST_LINE also needs to be set",
                    );
                    let line = isize::from_str_radix(&line, 10)
                        .expect("UNSTABLE_RUSTDOC_TEST_LINE needs to be an number");
                    rustc_span::FileName::doc_test_source_code(std::path::PathBuf::from(path), line)
                }
                Err(_) => rustc_span::FileName::anon_source_code(&input),
            };

            Some(rustc_session::config::Input::Str { name, input })
        }
        [ifile] => Some(rustc_session::config::Input::File(
            std::path::PathBuf::from(ifile),
        )),
        [ifile1, ifile2, ..] => early_dcx.early_fatal(format!(
            "multiple input filenames provided (first two filenames are `{}` and `{}`)",
            ifile1, ifile2
        )),
    }
}

fn make_output(
    matches: &rustc_session::getopts::Matches,
) -> (
    Option<std::path::PathBuf>,
    Option<rustc_session::config::OutFileName>,
) {
    let odir = matches
        .opt_str("out-dir")
        .map(|o| std::path::PathBuf::from(&o));
    let ofile = matches.opt_str("o").map(|o| match o.as_str() {
        "-" => rustc_session::config::OutFileName::Stdout,
        path => rustc_session::config::OutFileName::Real(std::path::PathBuf::from(path)),
    });
    (odir, ofile)
}

pub fn diagnostics_registry() -> rustc_errors::registry::Registry {
    rustc_errors::registry::Registry::new(rustc_errors::codes::DIAGNOSTICS)
}

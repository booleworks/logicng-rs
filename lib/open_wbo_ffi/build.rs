use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=open_wbo_wrapper/library.cpp");
    println!("cargo:rerun-if-changed=open_wbo_wrapper/include/library.h");

    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let lib_name = format!("_{os}_{arch}_open_wbo");
    let lib_file_name = format!("lib{lib_name}.a");

    let open_wbo_path = std::path::Path::new("open_wbo/");
    let out_dir = env::var("OUT_DIR").expect("$OUT_DIR is not set");
    let lib_path = PathBuf::from(&out_dir).join(lib_file_name);
    if !lib_path.exists() {
        build_open_wbo(open_wbo_path, &lib_path, &os, &arch);
    }

    //Link OpenWBO Library
    println!("cargo:rustc-link-search={}", out_dir);
    println!("cargo:rustc-link-lib=static={lib_name}");

    //Link other stuff
    if os == "linux" {
        println!("cargo:rustc-link-lib=gmpxx");
        println!("cargo:rustc-link-lib=gmp");
    }

    //Build Bridge between OpenWBO Wrapper and LogicNG
    let mut build = cxx_build::bridge("src/lib.rs");
    build
        .include(open_wbo_path.join("include/"))
        .flag("-w") //Suppress warnings
        .file("open_wbo_wrapper/library.cpp");

    if os == "macos" && arch == "aarch64" {
        build.include("/opt/homebrew/include");
    }

    if build.get_compiler().is_like_clang() || build.get_compiler().is_like_gnu() {
        build.flag("-std=c++11");
    } else {
        build.flag("/std:c++14"); //MSVC doesn't support c++11, but c++14 should also work.
    };
    build.compile("open_wbo_wrapper");
}

fn build_open_wbo(open_wbo_path: &std::path::Path, lib_path: &std::path::Path, os: &str, arch: &str) {
    let open_wbo_src_path = open_wbo_path.join("logicng-open-wbo");
    if !open_wbo_src_path.exists() {
        panic!("Cannot build OpenWBO, because the source code is missing.")
    }

    //Building OpenWBO Library
    let mut make = std::process::Command::new("make");
    if os == "macos" && arch == "aarch64" {
        make.env("CPATH", "/opt/homebrew/include");
    }
    make.current_dir(&open_wbo_src_path).arg("libr");
    if let Err(e) = make.status() {
        panic!("Building OpenWBO failed with: {}", e);
    }
    let lib_src_path = open_wbo_src_path.join("lib_release.a");
    if let Err(e) = std::fs::copy(lib_src_path, lib_path) {
        panic!("Building OpenWBO failed with: {}", e);
    }

    //Cleanup build files
    let mut dirs = Vec::new();
    dirs.push(open_wbo_src_path);
    while let Some(dir) = dirs.pop() {
        for entry in dir.read_dir().unwrap() {
            let e = entry.unwrap().path();
            let is_build_file = matches!(e.extension().map(|c| c.to_str()), Some(Some("a" | "o" | "or" | "od")));
            let is_depend_file = matches!(e.file_name().map(|c| c.to_str()), Some(Some("depend.mk")));
            if is_build_file || is_depend_file {
                if let Err(e) = std::fs::remove_file(e) {
                    panic!("Building OpenWBO failed with: {}", e);
                }
            } else if e.is_dir() {
                dirs.push(e);
            }
        }
    }
}

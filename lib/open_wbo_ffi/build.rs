use std::path::{Path, PathBuf};
use std::{env, fs};

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
    let operating_path = PathBuf::from(&out_dir);
    let lib_path = operating_path.join(lib_file_name);
    if !lib_path.exists() {
        build_open_wbo(open_wbo_path, &lib_path, &operating_path.join("logicng-open-wbo-src"), &os, &arch);
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

fn build_open_wbo(open_wbo_path: &std::path::Path, lib_path: &std::path::Path, operating_path: &std::path::Path, os: &str, arch: &str) {
    let open_wbo_src_path = open_wbo_path.join("logicng-open-wbo");
    if !open_wbo_src_path.exists() {
        panic!("Cannot build OpenWBO, because the source code is missing.")
    }

    copy_src(&open_wbo_src_path, operating_path);

    //Building OpenWBO Library
    let mut make = std::process::Command::new("make");
    if os == "macos" && arch == "aarch64" {
        make.env("CPATH", "/opt/homebrew/include");
    }
    make.current_dir(operating_path).arg("libr");
    if let Err(e) = make.status() {
        panic!("Building OpenWBO failed with: {}", e);
    }
    let lib_src_path = operating_path.join("lib_release.a");
    if let Err(e) = std::fs::copy(lib_src_path, lib_path) {
        panic!("Building OpenWBO failed with: {}", e);
    }

    //Cleanup build files
    if let Err(e) = fs::remove_dir_all(operating_path) {
        panic!("Building OpenWBO failed with: {}", e)
    }
}

fn copy_src(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("Couldn't create root directory");
    for entry in fs::read_dir(src).expect("Couldn't read directory") {
        let entry = entry.expect("Couldn't read file");
        let ty = entry.file_type().expect("Couldn't access filetype");
        if ty.is_dir() {
            copy_src(&entry.path(), &dst.join(entry.file_name()));
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name())).expect("Couldn't copy file");
        }
    }
}

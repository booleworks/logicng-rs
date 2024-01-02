use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=sharp_sat_wrapper/library.cpp");
    println!("cargo:rerun-if-changed=sharp_sat_wrapper/include/library.h");

    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let lib_name = "_sharp_sat";

    let sharp_sat_path = std::path::Path::new("sharp_sat/");
    let build_dst = build_sharp_sat(sharp_sat_path);
    //Link SharpSat
    println!("cargo:rustc-link-search={}", build_dst.join("build").display());
    println!("cargo:rustc-link-lib=static={lib_name}");
    if os == "macos" && arch == "aarch64" {
        println!("cargo:rustc-link-search=/opt/homebrew/include/Cellar/gmp/6.3.0/include");
    }

    //Link other stuff
    println!("cargo:rustc-link-lib=gmpxx");
    println!("cargo:rustc-link-lib=gmp");

    //Build Bridge between SharpSAT Wrapper and LogicNG
    let mut build = cxx_build::bridge("src/lib.rs");
    build.include(sharp_sat_path.join("include/")).flag("-w").file("sharp_sat_wrapper/library.cpp");

    if os == "macos" && arch == "aarch64" {
        build.include("/opt/homebrew/include");
    }

    if build.get_compiler().is_like_clang() || build.get_compiler().is_like_gnu() {
        build.flag("-std=c++11");
    } else {
        build.flag("/std:c++11");
    }
    build.compile("sharp_sat_wrapper");
}

fn build_sharp_sat(sharp_sat_path: &std::path::Path) -> PathBuf {
    let sharp_sat_src_path = sharp_sat_path.join("logicng-sharp-sat");
    if !sharp_sat_src_path.exists() {
        panic!("Cannot build SharpSAT, because the source code is missing.");
    }

    cmake::build(sharp_sat_path)
}

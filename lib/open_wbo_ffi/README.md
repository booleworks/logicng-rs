## Low Level LogicNG Bindings for OpenWBO

Low level Rust bindings for the MaxSAT solver
[Open-WBO](https://github.com/sat-group/open-wbo).  This crate is used within
the logic library [LogicNG](https://github.com/booleworks/logicng-rs.git) by
activating the feature `open_wbo`.

## Installation

This crate builds the Open-WBO solver from source.  There is a LogicNG-specific
fork of the solver in this
[repository](https://github.com/booleworks/logicng-open-wbo) which is used in
this build step.

Building is tested on macOS and Linux and should usually just require an
installed C++ compiler toolchain an the GMP library which can be installed e.g.
on macOS with the popular package manager [Homebrew](https://brew.sh/)

```bash
brew install gmp
```

or on Debian-based systems:

```bash
apt-get install libgmp3-dev
```

Windows ist currently only supported via the Windows Subsystem for Linux (WSL).

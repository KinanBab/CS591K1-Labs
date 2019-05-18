# BU CAS CS 591 K1 Labs - Foundations and Pragmatics of Dependently-Typed Automated Systems

This repository contains the lab notes and code for CS 591 K1, organized chronologically by topic.

The repository contains code samples in Coq, ATS, Agda, and Lean, in the order covered by the class.

## Installation - VirtualBox Image

We provide a [VirtualBox VDI image](https://www.dropbox.com/s/291i8w6eglnppa8/CS591K1.zip) shipped with working installations of all the languages and tools we use (UPDATE: The virtual image has been removed due to filling up dropbox, if you need it, drop me a line).
Uncompress the downloaded zip archive in a location of choosing, open the directory, and double click on CS591K1.vbox
to run the virtual image with VirtualBox. The image contains Ubuntu 18.04.1 X64, with a single user `cs591k1` and password `cs591k1`. 

You can download VirtualBox from [here](https://www.virtualbox.org/wiki/Downloads). The image already has VirtualBox's guest-additions installed,
which supports bi-directional shared clipboard and file drag-and-drop, so that the virtual machine and your host operating system can interact smoothly.
Additionally, a permenant auto-mount shared folder pointing to a dummy location on the host machine is included in the image. To use it, change the location it
points to under Shared Folders tab in the image settings inside Virtual box.

## Installation - Without VirtualBox Image

If you do not want to use the image, you can download each tool separately on your machine using the following instructions.

### Coq

We use the latest Coq version (Coq 8.8.2). If you are using Windows or Mac, you can install Coq by using the appropriate installer [file](https://github.com/coq/coq/releases/tag/V8.8.2). 
On Linux and mac, we recommend [installing Coq with OPAM](https://coq.inria.fr/opam/www/using.html) (OCaml package manager).

You can either use CoqIDE or Proof General to edit coq files interactively. CoqIDE comes built in with coq, but can be unresponsive or slow sometimes.
Proof General is an Emacs interface to simplify editing and running Coq files, you can download it using these [instructions](https://proofgeneral.github.io/).
Both editors are shipped with our VirtualBox image. We recommend using Proof General, since we will be using emacs for the other theorem provers as well.

### Lean

We use the latest Lean version (Lean 3.4.1). You can download it from [here](https://leanprover.github.io/download/).
You can use the emacs [lean-mode](https://github.com/leanprover/lean-mode) to facilitate using lean with emacs, or you can
use [Lean's Virtual Studio extension](https://marketplace.visualstudio.com/items?itemName=jroesch.lean) to edit Lean proofs
within the Virtual Studio IDE.

### Agda

We use the latest Agda version (Agda 2.5.4.2), We recommend installing Agda using Haskel's package manager Hackage. To use hackage, you must install these 
[prerequisites](https://agda.readthedocs.io/en/latest/getting-started/prerequisites.html#prerequisites). After installing the prerequisites, follow these
[instructions](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installation-from-hackage) to install Agda, and Emacs' 
agda-mode to facilitate editing Agda scripts. We will use the Agda standard library frequently, follow these [instructions](https://github.com/agda/agda-stdlib)
to install it, use version 0.17 and not version 1.0. Be sure to add it to the defaults file, so that it is included with all Agda projects by default.

### ATS

We use the latest (pre-stable) ATS version (ATS2-0.3.13). We recommend using 
[C9-ATS2-install-latest.sh](https://github.com/ats-lang/ats-lang.github.io/tree/master/SCRIPT) script
to download ATS if using ubuntu. We will frequently rely on Z3 to solve constraints automatically,
install the [Z3](https://github.com/Z3Prover/z3/releases) theorem prover.

If you are not using ubuntu, you will need to perform these steps:
1. Install these dependencies: build-essential libgmp-dev libgc-dev libjson-c-dev (or equivalent for your platform)
2. Git Clone ATS source code from source forge: git://git.code.sf.net/p/ats2-lang/code or 
download from [here](https://sourceforge.net/projects/ats2-lang/files/ats2-lang/).
3. Git clone ATS-contrib: https://github.com/githwxi/ATS-Postiats-contrib.git
4. You need to export 2 environment variables:
   PATSHOME=<path>/<to>/<ATS>
   PATSCONTRIB=<path>/<to>/<ATS-contrib>
   Additionally, you must append <path>/<to>/<ATS>/bin to the PATH environment variable.
5. inside the <ATS> directory, run ./configure and make all, this will essentially compile ATS
6. Compile ATS Z3 extension by running make DATS\_C, make all, and make all in <ATS>/contrib/ATS-extsolve, 
<ATS>/contrib/ATS-extsolve-z3, and <ATS>/contrib/ATS-extsolve-smt2 respectively. Move bin/patsolve\_z3 and bin/patsolve\_smt2 
from the last two directories to <ATS>/bin.
7. run make all and move the result binaries to <ATS>/bin inside <ATS>/contrib/CATS-parsemit and ATS/contrib/CATS-atscc2py3

Note: on some systems, installing Z3 will only install a libz3.so shared object file, ATS requires libz3.so.4.8. You can solve
this by creating a symbolic link (shortcut) or copying libz3.so to libz3.so.4.8 in the same directory it is installed in
(by default /usr/lib/ in unix systems).

These commands should run fine on macOS and the various linux distributions, if using windows, install and use 
[cygwin](https://cygwin.com/install.html), to mimic a unix shell environment.

# Compiling and Running Lab and Homework Code

## Coq
We use some of the definitions and tactics from Adam Chlipala's [FRAP Coq Library](https://github.com/achlipala/frap). It is included as a git submodule within
this repository, you need to initialize this submodule and compile the library the first time you clone this repo using:
```bash
git clone https://github.com/KinanBab/CS591K1-Labs <path>/<to>/<repo> # clone this repo
cd <path>/<to>/<repo>
git submoudle init # initialize the FRAP submodule
git submodule update # pulls the correct version the FRAP library
cd FRAP
make lib # compile the FRAP library
```

After having compiled FRAP, you will need to compile any lab code you wish to run, to do that, run `make` inside the code directory of the desired lab. After the code is compiled, you can open any desired .v file with coqide or proof general, and go through the file interactively.
```bash
cd /lab1/code # go to that the lab code
make # compile all the dependencies
```

For homework, You need to compile the provided modeling and problem statement code, before being able to use them in your solutions. Coq library/modules systems requires that any module you include be already compiled into a .vo file. You can do that by using the provided Makefiles.
```bash
cd /homework1/Problem1 # go to some homework problem
make # compile all the dependencies.
# Now you can edit Solution.v interactively using CoqIDE or proof-general
```

Check out the content of the Makefiles inside the lab and homework code directories to see how to compile manually from the command line, and Check out the \_CoqProject files to see how to define a Coq project with modules and dependencies.

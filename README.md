# BU CAS CS 591 K1 Labs - Foundations and Pragmatics of Dependently-Typed Automated Systems

This repository contains the lab notes and code for CS 591 K1, organized chronologically by topic.

The repository contains code samples in Coq, ATS, Agda, and Lean, in the order covered by the class.

## Installation - VirtualBox Image

We provide a VirtualBox VDI image shipped with working installations of all the languages and tools we use. The image contains Ubuntu 18.04.1 X64, with
a single user `cs591k1` and password `cs591k1`. 

You can download VirtualBox from [here](https://www.virtualbox.org/wiki/Downloads). The image already has VirtualBox's guest-additions installed,
which supports bi-directional shared clipboard and file drag-and-drop, so that the virtual machine and your host operating system can interact smoothly.
Additionally, a permenant auto-mount shared folder pointing to a dummy location on the host machine is included in the image. To use it, change the location it
points to under Shared Folders tab in the image settings inside Virtual box.

## Installation - Without VirtualBox Image

If you do not want to use the image, you can download each tool separately on your machine using the following instructions.

### Coq

We use the latest Coq version: Coq 8.8.2. If you are using Windows or Mac, you can install Coq by using the appropriate installer [file](https://github.com/coq/coq/releases/tag/V8.8.2). 
On Linux and mac, we recommend [installing Coq with OPAM](https://coq.inria.fr/opam/www/using.html) (OCaml package manager).

You can either use CoqIDE or Proof General to edit coq files interactively. CoqIDE comes built in with coq, but can be unresponsive or slow sometimes.
Proof General is an Emacs interface to simplify editing and running Coq files, you can download it using these [instructions](https://proofgeneral.github.io/).
Both editors are shipped with our VirtualBox image. We recommend using Proof General, since we will be using emacs for the other theorem provers as well.

We use some of the definitions and tactics from Adam Chlipala's [FRAP Coq Library](https://github.com/achlipala/frap). It is included as a git submodule within
this repository, you need to initialize this submodule and compile the library the first time you clone this repo using:
```bash
git clone https://github.com/KinanBab/CS591K1-Labs <path>/<to>/<repo> # clone this repo
cd <path>/<to>/<repo>
git submodule update # initialize the FRAP submodule
cd FRAP
make lib # compile the FRAP library
```

### Lean

Lean 3.4.1

ATS2-0.3.12

Agda 2.6.0

Since we rely on the Adam Chlipala's [FRAP]() library for Coq. 



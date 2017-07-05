SABLE Model
=================

Overview
-----------------

This is a multi-layer model of the Syracuse Assured Bootloader Executive
(SABLE), a bootloader which uses a TPM chip to establish mutual trust between
a computer system and its user. The model employs the following abstraction
hierarchy (listed in descending order of abstraction):
- Abstract, nondeterministic specification
- AutoCorres, deterministic specification
- C-SIMPL translated implementation
High-level properties of are proved at the Abstract level, and corresponding
behavior at the lower levels is established via data refinement.

Requirements
----------------

- The SABLE source code
- Isabelle/HOL 2016-1
- AutoCorres v1.3, which can be acquired
[here](http://ts.data61.csiro.au/projects/TS/autocorres/). You must launch
Isabelle/JEdit with the AutoCorres heap in order to load the SABLE .thy files.
Follow the directions in the AutoCorres README to build and test an AutoCorres
heap image.

Installation
----------------

To configure the project:

1. Obtain the SABLE source code, and follow the directions in the README to
   build the `sable-isa` target. In the `sable-model/` directory, create a new
   directory `src/` and copy `sable_isa.c` to `sable-model/src/`.
2. In your Isabelle application directory, add the line
   ```
   L4V_ARCH="ARM"
   ```
   to your `etc/settings` file.

Usage
---------------

First, make sure that the `isabelle`
executable is in your `$PATH`:
```bash
$ which isabelle
```
If this command returns nothing, you need to either symlink the
Isabelle executable into a directory along your path (e.g.
`/usr/local/bin`, or modify your `$PATH` to include the directory
where isabelle was installed.

### Isabelle/JEdit IDE

Navigate to the directory where AutoCorres was installed, and enter
```
$ isabelle jedit -d . -l AutoCorres
```
to launch Isabelle with the AutoCorres heap. Then navigate to the
`sable-model/` directory within JEdit, and you should be able to
load any of the .thy files without any issues.

### CLI Build

You can build the SABLE proofs from the command line with the
`isabelle build` utility. Navigate to the `sable-model/` directory,
and enter the following command:
```bash
$ isabelle build -d <path-to-autocorres> -d . -l AutoCorres SABLE
```
This process may take several minutes to complete. For any stable
build of SABLE, this should not yield any errors.

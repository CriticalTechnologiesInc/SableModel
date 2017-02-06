Simple Refinement
=================

Overview
-----------------

This is a multi-layer model of a simple cryptographic device and
an associated software driver, with the following abstraction
hierarchy (listed in descending order of abstraction):
- Access Control Logic (ACL)
- Abstract, nondeterministic specification
- AutoCorres, deterministic specification
- C-SIMPL translated implementation
High-level properties of are proved at the ACL level, and corresponding
behavior at the lower levels is established via data refinement.

The objective of this project is to demonstrate the data refinement
technique for complex, low-level projects written in C which interact
with external hardware device(s).

Requirements
----------------

- Isabelle/HOL 2016
- AutoCorres v1.2, which can be acquired
[here](http://ts.data61.csiro.au/projects/TS/autocorres/). You must launch
Isabelle/JEdit with the AutoCorres heap in order to load the .thy files.
Follow the directions in the AutoCorres README to build and test an AutoCorres
heap image.

Installation
----------------

To configure the project:

1. Obtain simple-refinement and library dependencies:
   ```
   $ git clone <url-to-simple-refinement>
   $ cd simple-refinement
   $ cd src/
   $ make
   $ cd ../lib/
   $ git clone <url-to-ACL>
   $ cd ACL/isabelle
   $ make
   ```
2. In your Isabelle application directory, add the line
   ```
   L4V_ARCH="ARM"
   ```
   to your `etc/settings` file.

Usage
---------------

Navigate to the directory where AutoCorres was installed, and enter
```
$ isabelle jedit -d . -l AutoCorres
```
to launch Isabelle with the AutoCorres heap. Then navigate to the
`simple-refinement/` directory within JEdit, and you should be able to
load any of the .thy files without any issues.

# Verification of Red-Black Trees in KeY
This repository contains a Java implementation of red-black trees, verified with KeY (https://github.com/KeYProject/key).
It is the result of my bachlor's thesis *Verification of Red-Black Trees in KeY – A Case Study in Deductive Java Verification*.

## Contents of this Repository
It consists of the following files:
- the three classes of the implementation, `Client`, `RBTree` and `Tree` are stored in the `src` folder, complete with their specification and JML Scripts
- `iSet.key` provides the definition of the custom integer set type that was used for the specification
- `project.key` is needed for loading a new method contract into key
- `key-2.13.0-exe.jar` provides the KeY version with which all proofs can be successfully loaded and replayed.\
  It was built using the commit `4d5d8c5c` from the `pfeifer/jmlScripts` branch in GitLab: https://git.key-project.org/key/key/-/commit/4d5d8c5cb0b36bcbdc74ead5888a2f6bbedfe5ef 
- the `proof` folder contains all proofs, grouped by their class

## Loading Proofs
To load and replay the proofs, clone this repository, execute the provided KeY-JAR, and choose the desired `.proof` file through `File > Load`.

## Some additional remarks:
- All `.proof` files are named after the method whose contract they prove. Methods having an `accessible` clause have an additional file with an `_accessible` suffix.
- Files with the prefix `acc_` contain proofs of the `accessible` clauses of model methods.
- Files with the suffix `_auto` do not contain individual steps of a proof, but a one-line-script that invokes KeY's automatic when loading them. They can be proven without any interaction.
- The `Tree` class contains a lot of JML Scripts. As they are a new feature, there are some situations where they are not powerful enough yet to capture the manually performed steps or where some bugs hinder successful execution. These situations are marked by a `TODO` in the script.
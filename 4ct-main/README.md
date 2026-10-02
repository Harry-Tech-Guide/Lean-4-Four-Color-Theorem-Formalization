# A research project on the Four Color Theorem and computer-assisted proofs

This research project attempts to replicate and reinterpret the algorithms from the paper The Four Colour Theorem by Robertson, Sanders, Seymour and Thomas (J. Combin. Theory Ser. B 70, 2-44 (1997)). Robertson et al presented a family of 633 configurations that has the following two properties:
- All members of the family are **C-reducible* or **D-reducible**.
- The family is **unavoidable**.

Once these two properties of the family are verified, which can be done in a finite calculation, the four color theorem follows. Robertson et al wrote two C programs, `reduce.c` and `discharge.c`, that perform these verifications.

Steinberger in 2010 found another family of 2822 configurations that certifies the four color theorem, through the following two properties:
- All members of the family are **D-reducible**.
- The family is **unavoidable**.

Steinberger used essentially the same programs `reduce.c` and `discharge.c`, though he had to make a few trivial modifications to RSST's original `reduce.c`.

I reimplemented Robertson et al's D-reducibility-checking algorithm and verified that my algorithm gives the same results as theirs for configurations that are D-reducible. This is sufficient to verify that all 2822 members of Steinberger's family are D-reducible - a key component of his version of the proof of 4CT.

**Map of the repository**
- `RSST-code` contains Robertson et al's programs `reduce.c` and `discharge.c`.
- `Steinberger-code` contains Steinberger's modified versions of `reduce.c` and `discharge.c`.
- `code` contains my own reimplmentation of Robertson et al's `reduce.c`. It is written in C with a Python wrapper defining a Configuration Python class that allows easy interfacing with the configuration data structure in a Python-accessible programming environment. There are some Jupyter notebooks illustrating the use of the mixed C/Python libraries.
- `papers` contains the Robertson et al paper, Steinber's papers, and several other notes and papers.
- `configurations` contains the data files defining the Robertson et al and Steinberger configuration families.

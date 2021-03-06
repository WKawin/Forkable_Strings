# Forkable_Strings
This repo contains a short and incomplete Isabelle proof script for the section 4.2: Forkable Strings in Aggelos Kiayias et al's Ouroboros: A Provably Secure Proof-of-Stake Blockchain Protocol (it is still not up-to-date compared to https://eprint.iacr.org/2016/889.pdf)

- All definitions up to 4.16

- Still messy, I will clean and add more comments soon

- For document, it's "~/output/document.pdf"

## Current status
This work includes ongoing and messy work on the proofs of Proposition 4.17 and Lemma 4.18, and these are steps I try to follow

### Proposition 4.17:
A string w is forkable if and only if there is a closed fork F |- w for which margin(F) ≥ 0.

For the case of characteristic strings not having 0 is the trivial case [DONE] and in a process of proving other than that I now separate the proof in two parts following the original proof in the paper. 

(->) If a string w is forkable then there is a closed fork F |- w for which margin(F) ≥ 0.
 - build Function "toClosedFork" to have the unique prefix fork [BUILT]
 - prove that the output has at least two tines having reach greater than or equal to 0 [now I am proving this]
 - point out that these two tines are prefixes of those of two logest ones in the original fork

(<-) If there is a closed fork F |- w for which margin(F) ≥ 0 then a string w is forkable.
 - reverse mechanism to above
 - build "toFlatFork" by adding those two tines which have reach greater than or equal to 0 by enough nodes to get a flate fork 

### Lemma 4.18:
m(nil) = (0, 0) [DONE] and, for all nonempty strings w ∈ {0, 1}*,
m(w1) = (λ(w) + 1, µ(w) + 1), and
m(w0) = (λ(w) − 1, 0) if λ(w) > µ(w) = 0, (0, µ(w) − 1) if λ(w) = 0, (0, µ(w) − 1) if λ(w) = 0, (λ(w) − 1, µ(w) − 1) otherwise.
Furthermore, for every string w, there is a closed fork Fw |- w for which m(w) = (λ(Fw), µ(Fw)). [DONE for the nil case]

Proof by induction 
 - basis step: prove for m [] = (0,0)
 - inductive : by cases; however each case is exhaustive in the paper (still planing to reduce the excessive amount of work)

## Future goals
Theorem 4.12: might follow this proof: https://eprint.iacr.org/2017/241 instead of the original one from the Ouroboros paper.

## Comments
- Working on GREATEST is quite tedious I am considering using Max instead as all sets considered should be finite.
- As the latest version updated section 4.2, there might be some other interesting proofs to be done after 4.17, 4.18 and 4.12


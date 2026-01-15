# Cellular Automata (and STAMs in general) as StreamGrids

## First idea: encoding a colouring
* Let `S = {s0, s1, ..., sn}` be the colours of the CA.
* Let `X = {x(n+1), x(n+2), ..., x(n+m)}` be '*things to colour*'.
* Use `S ++ X` as set to quotient.
* Let everything in `S` be a normal form.
* Set every `x ∈ X` equal to the desired colour in the qoutient.
    I.e., set `nf(x) = si` if `x` gets colour `si`.
* Now the StreamGrid encodes a decidable colouring `X -> S`.

## Application to cellular automata
* Let `S = {s0, s1, ..., sn}` be the colours of the CA.
* Let the space-time monoids be `M` and `T`, assume given by some signoid
    that enumerates all neighbours of `x ∈ M` at time `t` before enumerating `x`
    at time `t+1` (and generalise this to the case where `T` has mutliple
    generators).
* Colour the elements of `M` at time `0` according to a given initial
  configuration.
* Colour the other elements of `M` according to the local rule.
    This works because (given the right enumeration) we can look up the colours
    of neighbours in the input state.

## Questions
* Okay, we can encode all STAMs on enumerable (in a neighbourhood-respecting way
  of enumeration) space-time diagrams as StreamGrids this way. 
  Is that of any use or just a silly hack?
  One can probably hack the screens of the doors of the meeting rooms to play
  Tetris on them -- but that's not really a great contribution to society or
  philosophy. 

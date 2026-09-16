open Classical

variable (p : Prop)

#check em p
-- I'm struggling to keep all the examples within the same variable scope.
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases -- This is a tactic.
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction -- This is another tactic.
    (fun h1 : ¬p =>
     show False from h h1)

  /-I need to figure out how to understand each line.  I am not certain yet why these examples are "proofs". -/

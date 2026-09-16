import «Chapter 3 Practice».Basic
/- This is a project for me to go through the texts' third chapter-/
/- Below is the copy from the text to show this program runs-/
section first
def Implies (p q : Prop) : Prop := p → q
#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)

#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)
end first

section second
structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q

axiom modus_ponens (p q : Prop) : -- The idea is that given p and q, the proof of 'implies pq' implies that a proof of p implies a proof of q
  Proof (Implies p q) → Proof p →
  Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

#check implies_intro -- BTW, "a proof of something" is *also* a type.
-- Note that t : p is both "t of type p" and also p is a prop whose inhabitant is t.
end second

section third
set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
#print t1
end third

set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
theorem th1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem the1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := the1 hp

/- There are so many ways to write a theorem.  Let's try the next one:-/
theorem theo1 : ∀{p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

-- Try it with new variables!
variable (p q r s : Prop)

#check theo1 p q
#check theo1 r s
#check theo1 (r → s) (s → r)
variable (h : r → s)

#check theo1 (r → s) (s → r) h

variable (p q r s : Prop)

theorem tH2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
#check tH2

-- I am running out of dummy variables...ugh.  Time to understand And.intro--
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

-- Trying to prove 'or' using or.elim--
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

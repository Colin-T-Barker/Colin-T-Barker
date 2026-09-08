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

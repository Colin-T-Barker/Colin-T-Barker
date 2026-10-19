/- This is a set of exercises to test my proof in Lean prowess. -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
    Iff.intro -- this is telling LEAN to use an iff proof, LEAN expects both directions from functions
        (fun h: p ∧ q =>
            have hp : p := h.left
            have hq : q := h.right
            show q ∧ p from And.intro hq hp
        ) -- this closes the LHS of iff
        (
            fun h: q ∧ p =>
                have hq : q := h.left
                have hp : p := h.right
                show p ∧ q from And.intro hp hq
        ) -- this closes the RHS of iff
/- So the basic thing to learn here is that the way to think through this is to
    Tell the interpreter what to expect in terms of format, then describe the proof
    in terms of functions, etc.  I still need better info about what the ''.intro's are.-/


example : p ∨ q ↔ q ∨ p :=
    Iff.intro -- This just means I'm telling LEAN that we have to prove an iff statement.
        (fun h: p ∨ q => -- start with the LHS of the iff, name it h, and work with that.
            Or.elim h -- Begin the case by case proof...given p then q ∨ p,
            (fun hp => Or.inr hp) -- from h, I have p from Or.inr, this is enough to get q or p, injecting p into the RHS
            (fun hq => Or.inl hq) -- from h, I have q from Or.inl, this is enough to get q or p, injecting q into the LHS
        )  -- we can end the case here because we have checked both subcases that given one side of or you get the full or.
        (fun h: q ∨ p =>
            Or.elim h
            (fun hp => Or.inr hp)
            (fun hq => Or.inl hq)
        )
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
        (fun h: (p ∧ q) ∧ r =>
            have hpq : p ∧ q := h.left
            have hp : p := hpq.left
            have hq : q := hpq.right
            have hr : r := h.right
            show p ∧ (q ∧ r) from And.intro hp (And.intro hq hr)
        )
        (fun h: p ∧ (q ∧ r) =>
            have hp : p := h.left
            have hqr : q ∧ r := h.right
            have hq : q := hqr.left
            have hr : r := hqr.right
            show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr
        )
-- I'm pretty pleased with the above proof.  And understanding Or.elim better helps too.


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro -- tell Lean I'm doing an iff proof
        (fun h : (p ∨ q) ∨ r => -- start with the LHS →
            Or.elim h -- Since this is an ∨ we need to check the cases
                (fun hpq : p ∨ q => -- The LHS of h's ∨ is (p∨q)
                    Or.elim hpq -- We need to check the cases of hpq now
                        (fun hp => Or.inl hp) -- LHS of hpq gives us p which means from p we get p∨ "anything", in this case (q∨r)
                        (fun hq => Or.inr (Or.inl hq)) /- the new thing here is the way the function is written,
                        where we're telling it to inject q into the left of q∨r, and then
                        inject (q ∨ r) into the right of p∨ (q ∨ r).
                -/
                )
                (fun hr : r => Or.inr (Or.inr hr)) /- given r (the RHS of h) we first inject r into
                (q ∨ r)...that's the blue (), then we inject (q ∨ r) into p ∨ (q ∨ r).
                -/
        )
        (fun h : p ∨ (q ∨ r) =>
            Or.elim h -- Going from the RHS to the LHS that is ← '\ get'
                (fun hp: p => Or.inl (Or.inl hp)) /- for the other side of RHS, have p, so have
                p ∨ q and then inject p ∨ q into the left of the (p ∨ q) ∨ r. -/
                (fun hqr : (q ∨ r) => -- Apparently it is important to do LHS first for LEAN's or.elim
                    Or.elim hqr -- Still need to get q and r from this
                        (fun hq => Or.inl (Or.inr hq)) /- have q so we inject q into (p ∨ q)
                        then inject (p ∨ q) into the left of (p ∨ q) ∨ r -/
                        (fun hr => Or.inr hr) -- have r, so now I have (p ∨ q) ∨ r.
                )
        ) -- the lessons and keys here are: or.elim goes left to right, and inception injections.

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
        (fun h: p ∧ (q ∨ r) =>
            have hp: p := h.left
            have hqr: q ∨ r := h.right
            Or.elim hqr
                (fun hq => Or.inl (And.intro hp hq)) /- inject into the left of the '↔ ∨' statement
                (p∧q) which comes from having both p and q gives p∧q from and.intro.-/
                (fun hr => Or.inr (And.intro hp hr))
        )
        (fun h: (p ∧ q) ∨ (p ∧ r) =>
            Or.elim h
                (fun hpq =>
                    have hp: p := hpq.left
                    have hq: q := hpq.right
                    show (p ∧ (q ∨ r)) from And.intro hp (Or.inl hq) /- from hp we get p ∧ something.
                To have LEAN read p∧ (something) we need to use And.intro hp.  The (something)
                is q ∨ r, and we have q from hq, so we inject q into the left of q ∨ r using Or.inl hq.
                This gives us the full LHS of the '↔' statement, regardless of r's status.
                -/
                )
                (fun hpr =>
                    have hp: p := hpr.left
                    have hr: r := hpr.right
                    show (p ∧ (q ∨ r)) from And.intro hp (Or.inr hr)
                )
        )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro -- does iff go LHS to RHS too like Or.elim?
        (fun h: p ∨ (q ∧ r) =>
            Or.elim h
                (fun hp: p =>
                    And.intro (Or.inl hp) (Or.inl hp)
                )
                (fun hqr: q ∧ r =>
                    have hq: q := hqr.left
                    have hr: r := hqr.right
                    And.intro (Or.inr hq) (Or.inr hr)
                )
        )--now to the other side of the iff.

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

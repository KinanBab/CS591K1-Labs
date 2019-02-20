#check "hello world!"

/- 
C-c C-k shows how to type the symbol!
C-c C-x executes the entire script
C-c ! l shows the interactive panel below
-/

theorem t1 (p q : Prop) : p ∧ q → p ∧ q ∧ p :=
begin
  intros,
  apply and.intro,
  apply and.left a,
  apply and.intro,
  apply and.right a,
  apply and.left a,
end

theorem t2 (p q : Prop) (hp1: p) (hp2: q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  assumption,
  apply and.intro,
  assumption,
  assumption,
end

theorem t3 (p q: Prop) : p ∧ q → p ∧ q ∧ p :=
assume hpq: p ∧ q,
have h1: p, from and.left hpq,
have h2: q, from and.right hpq,
show p ∧ q ∧ p, from and.intro h1 (and.intro h2 h1)

theorem t4 (p q: Prop) (h: p ∧ q) : p ∧ q ∧ p :=
begin
  have h1: p, from and.left h,
  have h2: q, from and.right h,
  apply and.intro h1 (and.intro h2 h1),
end

/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .meet

open interval

-- the join connection

def join.horn {A : Type} (kan : has_hcom2 A)
  (p : I → A) : horn2 A :=
let u := horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl in
horn2.mk (λ _ _, p i0)
(meet kan p) (λ i _, p i) 
(meet kan p) (λ i _, p i)
((kan.eq0j (meet.horn kan p)).symm) rfl
((kan.eq0j (meet.horn kan p)).symm) rfl rfl
begin transitivity, apply kan.eq1i (meet.horn kan p), apply (kan.has1.t1 u) end
begin symmetry, transitivity, apply kan.eq1i (meet.horn kan p), apply (kan.has1.t1 u) end 
rfl

def join.filler {A : Type} (kan : has_hcom2 A)
  (p : I → A) : I → I → I → A :=
kan.hcom2 (join.horn kan p)

def join {A : Type} (kan : has_hcom2 A)
  (p : I → A) : I → I → A :=
(join.filler kan p) i1

--notation p `[` j `∨` i `]` kan := join kan p j i

namespace join

lemma face0i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : join kan p i0 = p :=
begin
  transitivity, apply kan.eq0j (join.horn kan p),
  transitivity, apply kan.eq1j (meet.horn kan p),
  apply (kan.has1.t1 (horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl))
end

lemma face1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : join kan p i1 = λ _, p i1 :=
kan.eq1j (join.horn kan p)

lemma face1j {A : Type} (kan : has_hcom2 A)
  (p : I → A) : (λ i, join kan p i i1) = λ _, p i1 :=
kan.eq1i (join.horn kan p)

lemma face0j {A : Type} (kan : has_hcom2 A)
  (p : I → A) : (λ i, join kan p i i0) = p :=
begin
  transitivity, apply kan.eq0i, -- (join.horn kan p)
  transitivity, apply kan.eq1j, -- (meet.horn kan p)
  apply (kan.has1.t1) -- (horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl)
end

end join

/-                   p                          --> i
        p i0 -----------------> p i1         j | 
         |                     ||              v
         |                     ||
         |                     ||
       p |      join p j i     || λ _, p i1
         |                     ||
         |                     ||
         v                     ||
        p i1 ================== p i1
                  λ _, p i1
-/

/-def test2 {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
join kan (λ (i : I), p @@ i) i0 i0 = eq.mp rfl (p@@i0) :=
begin
  rw join.face0i, refl --apply path.app0
end

def test3 {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
join kan (λ (i : I), p @@ i) i0 i1 = eq.mp rfl (p@@i1) :=
begin
  rw join.face0i, refl
end

def test31 {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  (λ i, p @@ i) i1 = eq.mp rfl (p @@ i1) :=
begin
  refl
end

variables {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b)

#check join kan (λ i, p@@i) i0
#check (λ i, p@@i)
#check @pathdp.abs
#check pathdp.abs (λ i, p@@i) rfl rfl
#check pathdp.abs (join kan (λ (i : I), p @@ i) i0) rfl rfl

def joinsquare22 {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  pathdp.abs (join kan (λ i, p@@i) i0) rfl rfl (test2 kan p) (test3 kan p) = 
  eq.mp (path.tyeq p) p :=
begin
  transitivity, apply pathdp.abseq, apply join.face0i, --rw pathdp.eta, 
  --have h : pathdp.abs (λ (i : I), p @@ i) rfl rfl _ _ = 
  --         pathdp.abs (λ (i : I), p @@ i) rfl rfl (pathdp.app0 p) (pathdp.app1 p) := 
  --         pathdp.abs_irrel,
  apply pathdp.abs_irrel', 
  --apply eq.mp, apply pathdp.abs_irrel,
  transitivity, exact pathdp.eta p rfl rfl (pathdp.app0 p) (pathdp.app1 p), 
end

def joinsquare {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  pathdp.abs (join kan (λ i, p@@i) i0) rfl rfl (test2 kan p) (test3 kan p) = 
  eq.mp (path.tyeq p) p :=
begin
  --induction ((join.face0i kan (λ i, p@@i)).symm),
  transitivity, apply pathdp.eta.eq, 
end

def tyeq_refl {A : I → Type} {A0 A1 : Type} {a : A i0} {b : A i1} (p : Π i, A i)
         {ha : A i0 = A i0} {hb : A i1 = A i1}
         (p0 : p i0 = eq.mp ha a) (p1 : p i1 = eq.mp hb b) : 
(pathd.tyeq (pathdp.abs p ha hb p0 p1)) = refl :=
sorry

def joinsquare'' {A : Type} {a b : A} (p : path A a b) :
  pathdp.abs (pathdp.app p) rfl rfl rfl rfl = eq.mp (pathd.tyeq p) p :=
begin
  induction p, --induction p_ha, 
  --induction (path.tyeq p),--induction p, 
  --induction ((join.face0i kan (λ i, p@@i)).symm),
end


def joinsquare' {A : Type} {a b : A} (p : path A a b) (q : I → A) 
  (h0 : q i0 = eq.mp rfl (p @@ i0)) (h1 : q i1 = eq.mp rfl (p @@ i1)) :
  pathdp.abs q rfl rfl h0 h1 = 
  eq.mp (path.tyeq p) p :=
begin
  --induction ((join.face0i kan (λ i, p@@i)).symm),
end
--calc
--  pathdp.abs (join kan (λ i, p@@i) i0) rfl rfl (test2 kan p) (test3 kan p) = 
--  pathdp.abs (λ i, p @@ i) rfl rfl rfl rfl : eq.rec _ (join.face0i kan (λ i, p@@i)).symm
--  ...                                                   = eq.mp (path.tyeq p) p : sorry

--eq.rec _ (join.face0i kan (λ i, p@@i)).symm
-- eq.rec (eq.rec _ (pathdp.eta p (pathdp.app0 p) (pathdp.app1 p))) (join.face0i kan (λ i, p@@i)).symm
-- (eq.rec _ (pathdp.eta (app p) (test2 kan p) (test3 kan p)))

--(eq.rec rfl (pathd.app0 p).symm) (eq.rec rfl (pathd.app1 p).symm)

def join0 {A : Type} {a b : A} (p : path A a b) : Type := 
pathdp (λ j, pathd (λ _, A) (p @@ j) b) p (path.refl b) 

--set_option pp.implicit true

lemma pathjoin {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  pathdp (λ j, pathd (λ _, A) (p @@ j) b) p (path.refl b) :=
begin
  fapply pathdp.abs,
    intro j, fapply pathdp.abs,
    intro i, apply join kan,
      apply (λ i, p @@ i), apply j, apply i,
      repeat {refl},
      apply (calc 
        join kan (λ i, p@@i) j i0 = (λ i, join kan (λ i, p@@i) i i0) j : rfl
        ...                       = p@@j : by rw join.face0j kan ),
      apply (calc 
        join kan (λ i, p@@i) j i1 = (λ i, join kan (λ i, p@@i) i i1) j : rfl
        ...                       = p@@i1 : by rw join.face1j kan 
        ...                       = b : by apply path.app1 ),
      --rw pathd.app0, refl,
      --rw pathd.app1, refl,
      exact (eq.rec rfl (pathd.app0 p).symm),
      exact (eq.rec rfl (pathd.app1 p).symm),
      --simp, simp, transitivity, --rw join.face0i, -- (join.face0i kan (app p)),
      simp, simp, 
      --rw join.face01 kan, 
      --exact (eq.rec (λ x, pathdp.abs x _ _ _ _ = eq.rec p (eq.rec rfl (pathd.app0 p).symm)) (join.face0i kan (app p)) )

      --rw join.face01 kan (@app (λ (_x : I), A) ((λ (_x : I), A) i0) ((λ (_x : I), A) i1) a b _ _ p),
      -- (@join A kan (@app (λ (_x : I), A) ((λ (_x : I), A) i0) ((λ (_x : I), A) i1) a b _ _ p)
      --apply pathdp.eta,
      
-- join kan (λ (i : I), p@@i) j i0 = p@@j
end
-/

/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.kan.coe ..core.connection.meet .groupoid.ops

open interval path

-- auxiliary definitions and lemmas

section

variable {A : Type}

private def f {a x y : A} (h : x = y) :
   path A a x → path A a y := 
λ p, eq.rec p h

private def f.eq {a x y : A} (h : x = y) (p : I → A) (h0 : p i0 = a) 
  (hx : p i1 = x) (hy : p i1 = y) : f h (abs p h0 hx ) = abs p h0 hy := 
by unfold f; induction h; simp

variable (kan : has_hcom2 A) 

private lemma aux {a b x : A} (p : path A a b) (h : b = x) 
  (ha : p @@ i0 = a) (hx : p @@ i1 = x) : f h p = path.abs (app p) ha hx :=
by unfold f; induction h; simp; symmetry; apply pathdp.eta

private lemma aux' {a b : A} (p : path A a b) (ha : meet kan (app p) i1 i0 = a) (hb : meet kan (app p) i1 i1 = p @@ i1) :
  f ((app1 p).symm) p = abs (meet kan (path.app p) i1) ha hb :=
by revert ha hb; refine eq.rec _ (meet.face1j kan (app p)).symm; intros; apply aux

lemma family.eq {a x y: A} (p : path A a x) (q : path A a y) (h : x = y) (h' : f h p = q) 
  {C : Π x : A, path A a x → Type} : C x p = C y q :=
by revert h'; unfold f; induction h; simp; intro; induction h'; refl

end

-- transport (coercion for paths)

section

variables {A : Type} (kan' : Π U, coe.has_coe U)

theorem path.transport {a x : A} (p : path A a x) (C : Π x : A, Type) 
  (u : C a) : C x :=
have C0 : C (p @@ i0) = C a := by rw app0 p,
have C1 : C (p @@ i1) = C x := by rw app1 p,
eq.mp C1 ((kan' (λ i, C (p @@ i) )).coe i0 (eq.mp C0.symm u) i1)

end

-- based path induction

variables {A : Type} (kan : has_hcom2 A) (kan' : Π U, coe.has_coe U)

theorem path.induction {a x : A} {C : Π x : A, path A a x → Type} 
  (p : path A a x) (u : C a (refl a)) : C x p :=
let X := path.abs (meet kan (app p) i0) 
  (eq.trans (meet.face0j0i kan (app p)) (app0 p)) 
  (eq.trans (meet.face0j1i kan (app p)) rfl) in
have h : f ((app0 p).symm) (path.refl a) = X, from
begin
  rw refl.eq (eq.trans (meet.face0j kan (app p)) (funext (λ i, app0 p))), 
  apply f.eq, transitivity, apply meet.face0j1i, apply app0
end,
let Y := abs (meet kan (app p) i1) 
  (eq.trans (meet.face1j0i kan (app p)) (app0 p)) 
  (eq.trans (meet.face1j1i kan (app p)) rfl) in
have h' : f ((app1 p).symm) p = Y, from
begin
  symmetry, apply abs_irrel, symmetry, apply aux',
  apply (eq.trans (meet.face1j0i kan (app p)) (app0 p)),
  apply (eq.trans (meet.face1j1i kan (app p)) rfl)
end,
have C0 : C a (refl a) = C (p @@ i0) _ := family.eq _ _ (app0 p).symm h,
have C1 : C x p = C (p @@ i1) _ := family.eq p _ (app1 p).symm h',
eq.mp C1.symm ((kan' (λ i, C (p @@ i) (path.abs (meet kan (app p) i) 
(eq.trans (meet.face0i' kan (app p) i) (app0 p) ) (meet.face1i' kan (app p) i) ))).coe 
i0 (eq.mp C0 u) i1)

/-def C0 {a x : A} {C : Π x : A, path A a x → Type} 
  (p : path A a x) : C a (path.refl a) = C (p @@ i0) _ :=
let X := path.abs (meet kan (app p) i0) 
  (eq.trans (meet.face0j0i kan (app p)) (app0 p)) 
  (eq.trans (meet.face0j1i kan (app p)) rfl) in
have h : f ((app0 p).symm) (path.refl a) = X, from
begin
  rw refl.eq (eq.trans (meet.face0j kan (app p)) (funext (λ i, app0 p))), 
  apply f.eq, transitivity, apply meet.face0j1i, apply app0
end,
family.eq _ _ (app0 p).symm h

variables {a x : A} {C : Π x : A, path A a x → Type} 
  (p : path A a x) (u : C a (path.refl a))

#check @path.induction
#check @C0
#check (eq.mp (C0 kan (refl a)) u)

#check (kan' (λ i, C (p @@ i) (path.abs (meet kan (app p) i) (eq.trans (meet.face0i' kan (app p) i) (app0 p) ) (meet.face1i' kan (app p) i) ))).coeq 
i0 (eq.mp (C0 kan p) u)

theorem path.induction.comp {a : A} {C : Π x : A, path A a x → Type} (u : C a (refl a)) : 
  path (C a (refl a)) (path.induction kan kan' (path.refl a) u) u :=
begin
  fapply path.abs, 
  --exact λ i, (kan' _).coe i0 i
end

-- eq.mp C1.symm (eq.mp C0 u) i1-/
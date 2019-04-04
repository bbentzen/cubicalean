/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import logic.function ...path.groupoid.ops

open interval

-- the meet connection

def meet.horn {A : Type} (kan : has_hcom2 A)
  (p : I →  A) : horn2 A :=
let u := horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl in
let meet' := kan.has1.hcom u in
horn2.mk (λ _ _, p i0) 
(λ _ _, p i0) (λ j i, meet' i j)
(λ _ _, p i0) (λ j i, meet' i j)
rfl ((kan.has1.t0 u).symm) rfl ((kan.has1.t0 u).symm)
rfl ((kan.has1.lid u).symm) (kan.has1.lid u) rfl

def meet.filler {A : Type} (kan : has_hcom2 A)
  (p : I → A) : I → I → I → A :=
kan.hcom2 (meet.horn kan p)

def meet {A : Type} (kan : has_hcom2 A)
  (p : I → A) : I → I → A :=
(meet.filler kan p) i1

--notation p `[` j `∧` i `]` kan := meet kan p j i  

namespace meet

lemma face0j {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i0 = λ _, p i0 :=
kan.eq0j (meet.horn kan p)

lemma face1j {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i1 = p :=
begin
  transitivity, apply kan.eq1j (meet.horn kan p),
  apply (kan.has1.t1 (horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl))
end

lemma face0i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : (λ i, meet kan p i i0) = λ _, p i0 := 
kan.eq0i (meet.horn kan p)

lemma face0i' {A : Type} (kan : has_hcom2 A)
  (p : I → A) (i : I) : meet kan p i i0 = p i0 :=
by revert i; apply function.funext_iff.1; apply face0i

lemma face1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : (λ j, meet kan p j i1) = p :=
begin
  transitivity, apply kan.eq1i (meet.horn kan p),
  apply (kan.has1.t1 (horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl))
end

lemma face1i' {A : Type} (kan : has_hcom2 A)
  (p : I → A) (i : I) : meet kan p i i1 = p i :=
by revert i; apply function.funext_iff.1; apply face1i

lemma face0j0i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i0 i0 = ( λ _, p i0) i0 :=
by apply function.funext_iff.1; apply face0j

lemma face0j1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i0 i1 = ( λ _, p i0) i1 :=
by apply function.funext_iff.1; apply face0j

lemma face1j0i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i1 i0 = p i0 :=
by rw face1j

lemma face1j1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i1 i1 = p i1 :=
by rw face1j

end meet

/-                λ _, p i1                      --> i
         p i1 ================== p i0         j | 
          ||                     |              v
          ||                     |
          ||                     |
λ _, p i1 ||      meet p j i     | p 
          ||                     |
          ||                     |
          ||                     v
         p i1 -----------------> p i1
                     p
-/

namespace refl

open path

lemma meet {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  path.refl a = abs (meet kan (app p) i0) 
                (eq.trans (meet.face0j0i kan (app p)) (app0 p)) 
                (eq.trans (meet.face0j1i kan (app p)) (app0 p)) :=
begin
  apply eq,
  transitivity,
  apply meet.face0j kan (app p),
  apply funext, intro, apply path.app0
end

end refl
/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.path ..default

open interval

-- weak connections

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
by revert i; apply funext_iff.1; apply face0i

lemma face1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : (λ j, meet kan p j i1) = p :=
begin
  transitivity, apply kan.eq1i (meet.horn kan p),
  apply (kan.has1.t1 (horn1.mk (λ _, p i0) (λ _, p i0) p rfl rfl))
end

------------------------

lemma face1i' {A : Type} (kan : has_hcom2 A)
  (p : I → A) (i : I) : meet kan p i i1 = p i :=
by revert i; apply funext_iff.1; apply face1i

lemma face0j0i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i0 i0 = ( λ _, p i0) i0 :=
by apply funext_iff.1; apply face0j

lemma face0j1i {A : Type} (kan : has_hcom2 A)
  (p : I → A) : meet kan p i0 i1 = ( λ _, p i0) i1 :=
by apply funext_iff.1; apply face0j

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

def both.horn {A : Type} (kan : has_hcom2 A)
  (p q : I → A) (h : p i1 = q i0) : horn2 A :=
begin
  fapply horn2.mk,
    exact (join kan p),
    exact (λ _, p), exact (meet kan q),
    exact (λ _, p), exact (meet kan q),
    rw join.face0i kan p,
    rw [join.face1i kan p, h, meet.face0j kan q],
    rw join.face0j kan p,
    rw [join.face1j kan p, h, meet.face0j kan q],
    refl,
    rw [h, meet.face0i kan q],
    rw [h, meet.face0i kan q],
    rw [meet.face1i kan q]
end

def both.filler {A : Type} (kan : has_hcom2 A)
  (p q : I → A) (h : p i1 = q i0)  : I → I → I → A :=
kan.hcom2 (both.horn kan p q h)

def both {A : Type} (kan : has_hcom2 A)
  (p q : I → A) (h : p i1 = q i0)  : I → I → A :=
both.filler kan p q h i1 

/-                     p                              --> i
          p i0 -----------------> p i1 = q i0      j | 
           |                      |                  v
           |                      |
           |                      |
         p |      both p j i      | q
           |                      |
           |                      |
           v                      v
  p i1 = q i0 -----------------> q i1
                  q
-/

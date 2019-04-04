/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

universes u

-- homogeneous Kan composition for lines and open boxes

open interval

structure horn1 (A : Type) :=
(lid t0 t1 : I → A)
(lid0 : lid i0 = t0 i0)
(lid1 : lid i1 = t1 i0)

prefix `⊔`:80 := horn1

structure has_hcom (A : Type) :=  
(hcom : ⊔ A → I → I → A)
(lid  : Π u, hcom u i0 = u.lid)
(t0   : Π u, (λ i, hcom u i i0) = u.t0)
(t1   : Π u, (λ i, hcom u i i1) = u.t1)
(eq0  : Π u, hcom u i1 i0 = u.t0 i1)
(eq1  : Π u, hcom u i1 i1 = u.t1 i1) 

def hcom {A : Type} (kan : has_hcom A) := kan.hcom 

notation `hcom` lid `[[` tube0 `;` tube1 `]]` kan :=  hcom kan (horn1.mk lid tube0 tube1 rfl rfl)

-- homogeneous Kan composition for squares and open cubes

structure horn2 (A : Type) :=
(lid t0i t1i t0j t1j : I → I → A) 
(lid0j : lid i0 = t0j i0)
(lid1j : lid i1 = t1j i0)
(lid0i : (λ j, lid j i0) = t0i i0)
(lid1i : (λ j, lid j i1) = t1i i0)
(t0i0j : (λ j, t0i j i0) = λ i, t0j i i0)
(t0i1j : (λ j, t0i j i1) = λ i, t1j i i0)
(t1i0j : (λ j, t1i j i0) = λ i, t0j i i1)
(t1i1j : (λ j, t1i j i1) = λ i, t1j i i1)

prefix `⊔`:80 := horn1

structure has_hcom2 (A : Type) :=
(hcom2 : horn2 A → I → I → I → A)
(lid : Π u : horn2 A, hcom2 u i0 = u.lid)
(t0j : Π u : horn2 A, (λ j, hcom2 u j i0) = u.t0j)
(t1j : Π u : horn2 A, (λ j, hcom2 u j i1) = u.t1j)
(t0i : Π u : horn2 A, (λ j i, hcom2 u j i i0) = u.t0i)
(t1i : Π u : horn2 A, (λ j i, hcom2 u j i i1) = u.t1i)
(eq0j : Π u : horn2 A, (hcom2 u i1) i0 = u.t0j i1)
(eq1j : Π u : horn2 A, (hcom2 u i1) i1 = u.t1j i1) 
(eq0i : Π u : horn2 A, (λ j, (hcom2 u i1) j i0) = u.t0i i1)
(eq1i : Π u : horn2 A, (λ j, (hcom2 u i1) j i1) = u.t1i i1)
(has1 : has_hcom A)

--TODO: define hcom for partially given horns and n-cubes

/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .terms

universes u v

-- homogeneous Kan composition for lines and open boxes

open interval

structure horn1 (A : 0-Type) := (lid t0 t1 : 1-(λ _, A)) 
(lid0 : lid i0 = t0 i0)
(lid1 : lid i1 = t1 i0) 

prefix `⊔`:80 := horn1

structure has_hcom (A : 0-Type) :=  
(hcom : ⊔ A → 2-(λ _ _, A))
(lid : Π u : ⊔ A, hcom u i0 = u.lid)
(t0 : Π u : ⊔ A, hcom u i0 = u.t0)
(t1 : Π u : ⊔ A, hcom u i1 = u.t1)
(eq0 : Π u : ⊔ A, hcom u i1 i0 = u.t0 i1)
(eq1 : Π u : ⊔ A, hcom u i1 i1 = u.t1 i1) 

def hcom {A : 0-Type} (kan : has_hcom A) := kan.hcom 

notation `hcom` lid `[[` tube0 `;` tube1 `]]` kan :=  hcom kan (horn1.mk lid tube0 tube1 rfl rfl)

-- coercion for n-cubes

namespace coe

structure has_coe {n} (A : I → n-Type) :=  
(coe : Π i, n-(A i) → Π j, n-(A j))
(coeq : Π i a, coe i a i = a)

end coe

-- homogeneous Kan composition for squares and open cubes

structure horn2 (A : 0-Type) := (lid t0i t1i t0j t1j : 2-(λ _ _, A)) 
(lid0j : lid i0 = t0j i0)
(lid1j : lid i1 = t0j i0)
(lid0i : (λ i, lid i i0) = t0i i0)
(lid1i : (λ i, lid i i1) = t1i i0)
(t0i0j : t0i i0 = λ i, t0j i i0)
(t0i1j : t0i i1 = λ i, t1j i i0)
(t1i0j : t1i i0 = λ i, t0j i i1)
(t1i1j : t1i i1 = λ i, t1j i i1)

prefix `⊔`:80 := horn1

structure has_hcom2 (A : 0-Type) :=  
(hcom2 : horn2 A → 3-(λ _ _ _, A))
(lid : Π u : horn2 A, hcom2 u i0 = u.lid)
(t0j : Π u : horn2 A, (λ j, hcom2 u j i0) = u.t0j)
(t1j : Π u : horn2 A, (λ j, hcom2 u j i1) = u.t1j)
(t0i : Π u : horn2 A, (λ j i, hcom2 u j i i0) = u.t0i)
(t1i : Π u : horn2 A, (λ j i, hcom2 u j i i1) = u.t1i)
(eq0j : Π u : horn2 A, (hcom2 u i1) i0 = u.t0j i1)
(eq1j : Π u : horn2 A, (hcom2 u i1) i1 = u.t1j i1) 
(eq0i : Π u : horn2 A, (λ j, (hcom2 u i1) j i0) = u.t0i i1)
(eq1i : Π u : horn2 A, (λ j, (hcom2 u i1) j i1) = u.t1i i1)

--TODO: define hcom for n-cubes
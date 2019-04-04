/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .join

open interval

-- the meet-and-join connection 

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

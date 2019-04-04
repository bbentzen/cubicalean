/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.interval

open interval

variables (A : I → I → Type) (a : Π j i, A j i)

-- adjacency conditions are immediate

example : a i0 i0 = (λ i, a i i0) i0 := rfl 

example : a i1 i0 = (λ i, a i i0) i1 := rfl

example : a i0 i1 = (λ i, a i i1) i0 := rfl

example : a i1 i1 = (λ i, a i i1) i1 := rfl

/-                                                                        

(λ i, a i1 i) i1 = (λ j, a j i1) i1 ======= (λ i, a i1 i) i1 = (λ j, a j i1) i1        --> i        
                ||                                              |                   j | 
                ||                                              |                     v
                ||                                              |
    λ j, a j i0 ||                     a                        | a j i1 
                ||                                              |
                ||                                              |
                ||                                              v
(λ i, a i1 i) i1 = (λ j, a j i1) i1 ======= (λ i, a i1 i) i1 = (λ j, a j i1) i1 

-/

-- faces and degeneracies 

example : (λ _, a) i0 = a := rfl 

example : (λ _, a) i1 = a := rfl 

example : (λ _, a i0) i1 = a i0 := rfl 
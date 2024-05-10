## group members
- Zhe Liu       (kyq5pg)
- Jin Yao       (rry4fg)
- Licheng Luo   (hvg7cb)

## what we achieved
In the AffineSpace.lean file, we first implemented vsub_Aff and created VSub instance using vsub_Aff. Moreover, we replaced the sorry inside the vsub_Aff with a proof.
After that we checked all constructors of all the classes we need to implement for implementing an AffineSpace, specifically, an AddTorsor over vector space. Specifically, we checked and analyzed the constructors of AddTorsor, AddGroup, SubNegMonoid, AddMonoid, AddSemigroup, Zero, Neg, Sub, AddAction, VAdd, VSub, Add and Nonempty, which are all required instances to implement a AddTorsor. 


After that, we implemented all the required instances above for getting an AddTorsor. Specifically, to implement VAdd, we defined function vadd_Aff for adding a affine vector with affine point to get an affine vector, then created VAdd instance using vadd_Aff. To implement Add, we defined function add_affine_vector for adding two affine vectors to get another affine vector, then created Add instance using add_affine_vector. Similarly, to define Zero instance we defined zero_affine_vector function, To define AddMonoid instance we defined affine_vector_nsmul, to define Neg we defined neg_affine_vector, to define SubNegMonoid we defined affine_vector_zsmul, etc. Finally, we successfully defined the AddTorsor instance based on Affine vector and Affine point, which reaches an Affine space.


Moreover, we implemented proofs to replace the sorry key words. For example, we replaced the sorry with the proof in vsub_Aff to prove the theorem of
List.length (List.zipWith (fun x x_1 => x - x_1) l1 l2) = n. We replaced the sorry with the proof in vadd_Aff to prove the theorem of List.length (List.zipWith (fun x x_1 => x + x_1) l1 l2) = n. We replaced the sorry with the proof in add_affine_vector to prove the theorem of List.length (List.zipWith (fun x x_1 => x + x_1) l1 l2) = n. We also implemented other required theorems like the proof in the neg_affine_vector for replacing the sorry keyword.


Furthermore, in the Main.lean file, we first defined several Affine vectors and Affine points for testing. After that we designed thorough test cases for testing the theorems and instances we defined in the  AffineSpace.lean file. Specifically, we defined the test cases for AddTorsor, AddGroup, SubNegMonoid, AddMonoid, AddSemigroup, Zero, Neg, Sub, AddAction, VAdd, VSub and Add, which can completely test the definition of our Affine space implemented. All the result of test cases were correct and, finally outputted to the terminal.

## what problems we run into
We met some problems when defining some of the proofs. The induction with Lean4 tactics does not work correctly sometimes. The problem is finally solved by using sorry keywords for some of the proofs. Therefore, it can ensure the final correct answer of all the test cases of our Affine Space.
namespace PrivateWitness

private def witnessNumber (n : Nat) := n + 7

theorem choose (n : Nat) : ∃ (_ : Nat), True := ⟨witnessNumber n, True.intro⟩

end PrivateWitness

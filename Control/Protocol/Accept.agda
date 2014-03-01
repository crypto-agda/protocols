
data Accept? : ★ where
  accept reject : Accept?

data Is-accept : Accept? → ★ where
  accept : Is-accept accept

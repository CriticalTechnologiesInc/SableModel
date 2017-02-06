theory ComExtensions
imports
  SimpleSimulation
  AutoCorres
begin

definition
  lift_com :: "('a, 'b, 'c) com \<Rightarrow> ('b \<Rightarrow> ('a, 'b, 'c) com option) \<Rightarrow> ('a \<times> 'a) set"
where
  "lift_com C \<Gamma> \<equiv> { (s, s'). \<Gamma> \<turnstile> \<langle>C, Normal s\<rangle> \<Rightarrow> Normal s' }"

end
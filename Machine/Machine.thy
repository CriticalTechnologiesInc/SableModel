theory Machine
imports
  TPM
begin

record machine_state =
  powerOn :: bool
  tpm :: tpm_state

type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

definition
  tpm_lift :: "'a tpm_monad \<Rightarrow> 'a machine_monad"
where
  "tpm_lift m \<equiv>
   do
    tpm_state \<leftarrow> gets tpm;
    (r, tpm_state') \<leftarrow> select_f (m tpm_state);
    modify (\<lambda>s. s \<lparr> tpm := tpm_state' \<rparr>);
    return r
   od"

lemma tpm_lift_wp[wp]:
  "(\<And>ss. \<lbrace>\<lambda>s. P (ss\<lparr> tpm := s \<rparr>)\<rbrace> m \<lbrace>\<lambda>r s'. Q r (ss\<lparr> tpm := s' \<rparr>)\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> tpm_lift m \<lbrace>Q\<rbrace>"
  unfolding tpm_lift_def apply wp unfolding valid_def
proof -
  fix s :: machine_state and r
  let ?tpm_state = "tpm s"
  assume a: "\<And>ss. \<forall>s. P (ss\<lparr>tpm := s\<rparr>) \<longrightarrow> (\<forall>(r, s')\<in>fst (m s). Q r (ss\<lparr>tpm := s'\<rparr>))"
     and "P s"
  have s: "s = s\<lparr>tpm := ?tpm_state\<rparr>" by auto
  with `P s` have "P (s\<lparr>tpm := ?tpm_state\<rparr>)" by presburger
  with a have "\<forall>(r, s')\<in>fst (m ?tpm_state). Q r (s\<lparr>tpm := s'\<rparr>)" by simp
  thus "\<forall>x\<in>fst (m (tpm s)). (case x of (r, tpm_state') \<Rightarrow> \<lambda>s. Q r (s\<lparr>tpm := tpm_state'\<rparr>)) s" by auto
qed

end
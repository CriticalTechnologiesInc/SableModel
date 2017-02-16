theory AMonad
imports
  "../lib/NondetExtensions"
  "../Machine/Machine"
begin

record Session =
  nonceEven :: NONCE
  nonceOdd :: NONCE
  continue :: bool

definition
  empty_Session :: "(TPM.AUTHHANDLE, Session) lookup"
where
  "empty_Session \<equiv> \<lambda>_. None"

definition
  update_Session :: "(TPM.AUTHHANDLE, Session) lookup \<Rightarrow> TPM.AUTHHANDLE \<Rightarrow> Session
    \<Rightarrow> (TPM.AUTHHANDLE, Session) lookup"
where
  "update_Session m h s \<equiv> \<lambda>h'. if h' = h then Some s else m h'"

record astate =
  machine :: machine_state
  sessions :: "(TPM.AUTHHANDLE, Session) lookup"

type_synonym 'a s_monad = "(astate, 'a) nondet_monad"

definition
  machine_op_lift :: "'a machine_monad \<Rightarrow> 'a s_monad"
where
  "machine_op_lift m \<equiv>
   do
    s \<leftarrow> gets machine;
    (r, s') \<leftarrow> select_f (m s);
    modify (\<lambda>s. s \<lparr> machine := s' \<rparr>);
    return r
   od"

lemma machine_op_lift_wp[wp]:
  "\<forall>ss. \<lbrace>\<lambda>s. P (ss\<lparr> machine := s \<rparr>)\<rbrace> m \<lbrace>\<lambda>r s'. Q r (ss\<lparr> machine := s' \<rparr>)\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> machine_op_lift m \<lbrace>Q\<rbrace>"
  unfolding machine_op_lift_def apply wp unfolding valid_def
proof -
  fix s :: astate and r
  let ?m_state = "machine s"
  assume a: "\<forall>ss s. P (ss\<lparr>machine := s\<rparr>) \<longrightarrow> (\<forall>(r, s')\<in>fst (m s). Q r (ss\<lparr>machine := s'\<rparr>))"
     and "P s"
  have s: "s = s\<lparr>machine := ?m_state\<rparr>" by auto
  with `P s` have "P (s\<lparr>machine := ?m_state\<rparr>)" by presburger
  with a have "\<forall>(r, s')\<in>fst (m ?m_state). Q r (s\<lparr>machine := s'\<rparr>)" by blast
  thus "\<forall>x\<in>fst (m (machine s)). (case x of (r, s') \<Rightarrow> \<lambda>s. Q r (s\<lparr>machine := s'\<rparr>)) s"
    by auto
qed

definition "m_tpm_lift \<equiv> machine_op_lift \<circ> tpm_lift"

definition
  exit :: "unit s_monad"
where
  "exit \<equiv> machine_op_lift $ modify (\<lambda>s. s\<lparr> powerOn := False \<rparr>)"

definition
  exit_r :: "'a s_monad"
where
  "exit_r \<equiv>
   do
    exit;
    unknown
   od"

end
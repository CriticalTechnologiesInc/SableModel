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
    mstate \<leftarrow> gets machine;
    (r, tpm_state') \<leftarrow> select_f (m mstate);
    modify (\<lambda>s. s \<lparr> machine := mstate \<rparr>);
    return r
   od"

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
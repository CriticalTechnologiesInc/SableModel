theory AMonad
imports
  "../lib/NondetExtensions"
  TPM
begin

record Session =
  nonceEven :: NONCE
  nonceOdd :: NONCE
  continue :: bool

definition
  Session_empty :: "(TPM.AUTHHANDLE, Session) lookup"
where
  "Session_empty \<equiv> \<lambda>_. None"

definition
  update_Session :: "(TPM.AUTHHANDLE, Session) lookup \<Rightarrow> TPM.AUTHHANDLE \<Rightarrow> Session
    \<Rightarrow> (TPM.AUTHHANDLE, Session) lookup"
where
  "update_Session m h s \<equiv> \<lambda>h'. if h' = h then Some s else m h'"

record astate =
  powerOn :: bool
  sessions :: "(TPM.AUTHHANDLE, Session) lookup"
  tpm :: tpm_state

type_synonym 'a s_monad = "(astate, 'a) nondet_monad"

definition
  tpm_lift :: "'a tpm_monad \<Rightarrow> 'a s_monad"
where
  "tpm_lift m \<equiv>
   do
    tpm_state \<leftarrow> gets tpm;
    (r, tpm_state') \<leftarrow> select_f (m tpm_state);
    modify (\<lambda>s. s \<lparr> tpm := tpm_state' \<rparr>);
    return r
   od"

definition
  reboot :: "unit s_monad"
where
  "reboot \<equiv> modify (\<lambda>s. s\<lparr> powerOn := False \<rparr>)"

end
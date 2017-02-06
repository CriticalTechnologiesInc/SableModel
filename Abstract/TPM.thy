theory TPM
imports
  "../lib/NondetExtensions"
begin

(* External Structures, from TPM Main Part 2 *)

datatype PCRINDEX = PCR0 | PCR1 | PCR2 | PCR3 | PCR4 | PCR5 | PCR6 | PCR7 | PCR8 | PCR9 | PCR10
| PCR11 | PCR12 | PCR13 | PCR14 | PCR15 | PCR16 | PCR17 | PCR18 | PCR19 | PCR20 | PCR21 | PCR22
| PCR23

type_synonym NV_INDEX = nat

datatype ERROR = AUTHFAIL | OTHER_ERROR

type_synonym RESULT = "ERROR + unit"
type_synonym AUTHHANDLE = nat

datatype NONCE = nonce nat

(* helper type *)
datatype dig =
  PCRINDEX_dig PCRINDEX
| NV_INDEX_dig NV_INDEX
| RESULT_dig RESULT
| AUTHHANDLE_dig AUTHHANDLE
| AUTHDATA_dig AUTHDATA
| NONCE_dig NONCE
| string_dig string
| nat_dig nat
| bool_dig bool
| DIGEST_dig "dig list"
and AUTHDATA = auth nat | hmac AUTHDATA "dig list"

type_synonym DIGEST = "dig list"

class Hashable =
  fixes hash :: "'a \<Rightarrow> DIGEST"
  assumes injective: "hash x = hash y \<Longrightarrow> x = y"

(* auxiliary TPM Structures *)

record Auth_in =
  authHandle :: AUTHHANDLE
  nonceOdd :: NONCE
  continueAuthSession :: bool
  auth :: AUTHDATA

record Auth_out =
  nonceEven :: NONCE
  continueAuthSession :: bool
  auth :: AUTHDATA

(* TPM State representation *)

(*record Session =
  nonceEven :: NONCE
  nonceOdd :: "NONCE option"

type_synonym Session_map = "AUTHHANDLE \<Rightarrow> Session option"

definition
  Session_empty :: Session_map
where
  "Session_empty \<equiv> \<lambda>_. None"

definition
  update_Session :: "Session_map \<Rightarrow> AUTHHANDLE \<Rightarrow> Session \<Rightarrow> Session_map"
where
  "update_Session m h s \<equiv> \<lambda>h'. if h' = h then Some s else m h'"

record tpm_state =
  sessions :: Session_map*)

type_synonym tpm_state = unit
type_synonym 'a tpm_monad = "(tpm_state, 'a) nondet_monad"

(* TPM Commands, from TPM Main Part 3 *)

record PCRRead_in =
  pcrIndex :: PCRINDEX

record PCRRead_out =
  returnCode :: RESULT
  outDigest :: DIGEST

definition
  PCRRead :: "PCRRead_in \<Rightarrow> PCRRead_out tpm_monad"
where
  "PCRRead com \<equiv> select (UNIV :: PCRRead_out set)"

record OIAP_out =
  returnCode :: RESULT
  authHandle :: AUTHHANDLE
  nonceEven :: NONCE

definition
  OIAP :: "OIAP_out tpm_monad"
where
  "OIAP \<equiv> unknown"

record NV_ReadValue_in =
  nvIndex :: NV_INDEX
  offset :: nat
  ownerAuth :: "Auth_in option"

record 'a NV_ReadValue_out =
  returnCode :: RESULT
  data :: 'a
  ownerAuth :: Auth_out

definition
  NV_ReadValue :: "NV_ReadValue_in \<Rightarrow> ('a NV_ReadValue_out) tpm_monad"
where
  "NV_ReadValue com \<equiv> unknown"

(*record OSAP_in =
  entityType

record OSAP_out =
  returnCode :: RESULT
  authHandle :: AUTHHANDLE
  nonceEven :: NONCE

definition
  OIAP :: "OIAP_out tpm_monad"
where
  "OIAP \<equiv> select (UNIV :: OIAP_out set)"

definition
  OIAP :: "OIAP_out tpm_monad"
where
  "OIAP \<equiv>
   do
    h \<leftarrow> select (UNIV :: AUTHHANDLE set);
    n \<leftarrow> select (UNIV :: NONCE set);
    modify (\<lambda>s. s\<lparr> sessions := update_Session (sessions s) h (S_OIAP n None) \<rparr>);
    return \<lparr>
      returnCode = Inr (),
      authHandle = h,
      nonceEven = n
    \<rparr>
   od"*)

end
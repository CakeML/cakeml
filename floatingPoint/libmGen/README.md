A libm-generator for CakeML that uses Dandelion and FloVer from `tools`
to prove a specification that relates CakeML code to the real-valued elementary
function.

[FloVerToCakeMLProofsScript.sml](FloVerToCakeMLProofsScript.sml):
Main connection theorem relating FloVer's roundoff error bound
to CakeML floating-point kernel executions

[FloVerToCakeMLScript.sml](FloVerToCakeMLScript.sml):
Translation from CakeML floating-point kernels to FloVer input

[cosExampleScript.sml](cosExampleScript.sml):
Example libm function generated from cosine certificate of Dandelion

[expExampleScript.sml](expExampleScript.sml):
Example libm function generated from cosine certificate of Dandelion

[libmLib.sml](libmLib.sml):
Implementation of automatic generation of libm functions

[libmScript.sml](libmScript.sml):
Supporting proofs for automation

[sinExampleScript.sml](sinExampleScript.sml):
Example libm function generated from sine certificate of Dandelion

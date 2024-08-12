// Adapted from dafny/firstSteps/2_Modules.dfy: removed class, replaced const
// by functions
module A {
	function i(): int { 1 }
}

module B {
  function i(): int { 2 }

  module X {
    function i(): int { 3 }
  }
}

module C {}

method Main(){
  print A.i(), " ", B.i(), " ", B.X.i(), "\n";
}

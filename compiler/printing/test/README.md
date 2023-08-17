Tests for the pretty-printer apparatus.

[printingTestScript.sml](printingTestScript.sml):
This file creates some sample declarations and runs the pretty
printer adjustments over them, confirms that the adjusted decs
still type check, and exports the s-expressions so that the
printed strings can be checked with the binary compiler.

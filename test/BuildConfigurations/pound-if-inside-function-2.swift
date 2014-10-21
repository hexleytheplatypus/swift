// RUN: %swift -D BLAH %s -verify -parse

// Check that if config statement has range properly nested in its parent
// EOF.

func foo() { // expected-note {{to match this opening '{'}}
#if BLAH
#elseif !BLAH
// expected-error@+2{{expected '}' at end of brace statement}}
// expected-error@+1{{expected #else or #endif at end of configuration block}}

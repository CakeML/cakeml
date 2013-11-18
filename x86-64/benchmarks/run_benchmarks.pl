#!/usr/bin/perl

use 5.010;
use strict;
use warnings;

sub bench {
    say "$_[0]:";
    system("cat poly_timer.sml $_[0].sml | poly | grep \"time:\" | sed 's/time:/  poly:    /g'");
    system("time -f '  ocaml:    %e' ocaml $_[0].ml");
    system("ocamlopt $_[0].ml -o a.out");
    system("time -f '  ocamlopt: %e' ./a.out ");
    system("rm -f a.out $_[0].cmi $_[0].cmx $_[0].o");
}

my $file;
foreach $file (<*.ml>) {
    $file =~ s/.ml$//g;
    bench($file);
}

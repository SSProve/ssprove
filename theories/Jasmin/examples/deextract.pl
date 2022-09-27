#!/usr/bin/perl
use Regexp::Common;

my $string = <>;

# change easy stuff (remove names added by extraction, quote strings, etc.)
$string =~ s/Jasmin\.[[:graph:]]*\.//g ;
$string =~ s/Coq_//g ;
$string =~ s/=/:=/g ;
$string =~ s/{/{| /g ;
$string =~ s/}/ |}/g ;
$string =~ s/v_info :=[ \t\n]*[^{}]*{[^}]*}/v_info := dummy_var_info/g ;
$string =~ s/(MkI[^(]*\()\(([^()]*(\([^)]*\))*)*\)/$1dummy_instr_info/g ;
$string =~ s/([[:alnum:]]*\.[[:alnum:]]*)/"$1"/g ;
$string =~ s/\(\)/tt/g ;

# curry functions
# pattern which matches balanced expression with either () {} or ""
my $bal = qr/$RE{balanced}{-parens=>'(){}""'}/;

# pattern which matches an alnum (function) followed by a tuple, e.g. f (a, b)
my $pat = qr/([[:alnum:]][ \n\t]*\(([^()]|($bal))*),([ \n\t]*)(([^(),]|($bal))*)\)/;

# propagate the final parenthesis of the tuple down and parenthesise:
# f (a, b, c) -> f (a, b) (c) -> f (a) (b) (c)
while ( $string =~ m/$pat/g ) {
    $string =~ s/$pat/$1\)$5\($6\)/g;
}

print($string);

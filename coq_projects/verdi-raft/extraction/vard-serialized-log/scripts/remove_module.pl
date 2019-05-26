#!/usr/bin/perl

use strict;
use warnings;

# https://perlmaven.com/how-to-replace-a-string-in-a-file-with-perl

my $serializer_name = $ARGV[0];
my $mli_name = $serializer_name . '.mli';

my $mli = read_file($mli_name);
$mli =~ s/module.*\n WRITER//g;
$mli =~ s/module.*\n READER//g;
write_file($mli_name, $mli);
exit;

sub read_file {
    my ($filename) = @_;
    
    open my $in, '<:encoding(UTF-8)', $filename or die "Could not open '$filename' for reading $!";
    local $/ = undef;
    my $all = <$in>;
    close $in;
    
    return $all;
}

sub write_file {
    my ($filename, $content) = @_;
    
    open my $out, '>:encoding(UTF-8)', $filename or die "Could not open '$filename' for writing $!";;
    print $out $content;
    close $out;
    
    return;
}

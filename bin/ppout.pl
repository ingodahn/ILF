# Nachbehandlung von ilf erzeugter {LaTeX, HTML, ...}-Files
# Aufruf: ppout -m mode -r RefFile [InputFile...]

$progname=$0;
$progname=~s/^.*\/([^\/].*)$/$1/;
@modes = qw(latex html text dyna);


while (@ARGV) {
	last unless $ARGV[0]=~/-(.)(.*)$/;
	shift(@ARGV);
	if ($1 eq 'm') {
		if (($mode=$2) eq '') {
			die "$progname: option -m needs an argument\n"
				unless defined($mode=shift(@ARGV));
		}
		grep /^$mode$/o, @modes or 
			warn "$progname: warning: $mode: unsupported output mode\n";
		defined(&{$fixline='fixline_'.$mode}) or
			$fixline='fixline';
		defined(&{$get_label='get_label_'.$mode}) or
			$get_label='get_label';
		defined(&{$begin_formula='begin_formula_'.$mode}) or
			$begin_formula='begin_formula';
		defined(&{$end_formula='end_formula_'.$mode}) or
			$end_formula='end_formula';
		defined(&{$begin_lab_formula = 'begin_lab_formula_'.$mode}) or
			$begin_lab_formula = 'begin_lab_formula';
		defined(&{$end_lab_formula = 'end_lab_formula_'.$mode}) or
			$end_lab_formula = 'end_lab_formula';
		defined(&{$unknown_ref = 'unknown_ref_'.$mode}) or
			$unknown_ref = 'unknown_ref';
	} elsif ($1 eq 'r') {
		if (($reffile=$2) eq '') {
			die "$progname: option -r needs an argument\n"
				unless defined($reffile=shift(@ARGV));
		}
	} else {
		&usage;
	}
}

@infiles=@ARGV;

defined($mode) or &usage;
defined($reffile) or &usage;

open(REFFILE, "<$reffile") or die "$progname: cannot open $reffile\n";

while (<REFFILE>) {
	chomp;
	last if /^$/;
	&$get_label;
}
while (<REFFILE>) {
	chomp;
	chomp($ref{$_}=<REFFILE>);
	chomp($ref_firstup{$_}=<REFFILE>);
}
close(REFFILE);
# unlink($reffile);

$nl=1;
$line = '';
while (<>) {
	chomp;
	if (/^ilf_include (.*)$/) {
		if (open INCLUDE, "<$1") {
			while (<INCLUDE>) {
				&fixline_and_print($_);
			}
			close INCLUDE;
		}
		$nl=0;
	} elsif (/^ilf_formula (.*)$/) {
		if ($label=$label{$1}) {
			&$begin_lab_formula;
	    	while (<>) {
	        	if (/^ilf_formula_end/) { &$end_lab_formula; $nl=0; last; }
				else { &fixline_and_print($_); }
	    	}
		} else {
	    	&$begin_formula;
	    	chomp($_=<>);
	    	&fixline_and_print($_);
	    	while (<>) {
				if (/^ilf_formula_end/) { &$end_formula; $nl=0; last; }
				else { chomp; &fixline_and_print("\n$_"); }
	    	}
		}
	} elsif (/^ilf_ref (.*)$/) {
		if ($ref=$ref{$1}) { &fixline_and_print($ref);} 
		else { &$unknown_ref; }
		$nl=0;
	} elsif (/^ilf_ref_firstup (.*)$/) {
		if ($ref=$ref_firstup{$1}) { &fixline_and_print($ref);} 
		else { &$unknown_ref; }
		$nl=0;
	} else {
		if ($nl) { &fixline_and_print("\n"); }
		else { $nl=1; }
		&fixline_and_print($_);
	}
}   
&fixline_and_print("\n");
# foreach $infile (@infiles) { unlink($infile); }

sub usage {
	die "usage: $progname -m mode -r RefFile [InputFile...]\n";
}

sub fixline_and_print {
	my $pos;
	$line .= $_[0];
	if (($pos = rindex $line, "\n") >= 0) {
		$pos++;
		$printline = substr $line, 0, $pos;
		&$fixline();
		print $printline;
		$line = substr $line, $pos;
	}
}

# Default
sub fixline { }
sub get_label { }
sub begin_lab_formula { }
sub end_lab_formula { }
sub begin_formula { }
sub end_formula { }
sub unknown_ref { }

# LaTex
sub fixline_latex { 
	$printline =~ s/\$\$//g; 
}
sub get_label_latex { $label{$_}=1; }
sub begin_lab_formula_latex { 
	&fixline_and_print("\n\\ilfformula{\\label{$1}\n"); 
}
sub end_lab_formula_latex { &fixline_and_print("}\n"); }
sub begin_formula_latex { &fixline_and_print("\$ "); }
sub end_formula_latex { &fixline_and_print(" \$"); }
sub unknown_ref_latex { &fixline_and_print("\\verb%$1%"); }

# HTML
sub get_label_html { chomp($label{$_}=<REFFILE>); }
sub begin_lab_formula_html { 
	&fixline_and_print(
		"<CENTER><TABLE><TR><TD WIDTH=500 ALIGN=CENTER><A NAME=\"$1\">\n");
}
sub end_lab_formula_html { 
	&fixline_and_print(
		"</A></TD><TD ALIGN=RIGHT>($label)</TD></TR></TABLE></CENTER>\n");
}
sub unknown_ref_html { &fixline_and_print("<CODE>$1</CODE>"); }

# dyna
sub fixline_dyna {
	s/<F><\/F>//g; 
	s/<\/F><F>//g;
}
sub get_label_dyna { chomp($label{$_}=<REFFILE>); }
sub begin_lab_formula_dyna { &fixline_and_print("<DF ID=\"$1\">\n"); }
sub end_lab_formula_dyna { &fixline_and_print("</DF>"); }
sub unknown_ref_dyna { &fixline_and_print("<CODE>$1</CODE>"); }

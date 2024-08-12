method Main() {
	print '\'';
	print ['\''];
	print "'";
	print ["'"];
	print @"'";
	print [@"'"];

	print "\n";

	print '\"';
	print ['\"'];
	print "\"";
	print ["\""];
	// These lines make Dafny crash
	// https://github.com/dafny-lang/dafny/issues/5677
	// print @"\";
	// print [@"\"];
	print @"\a";
	print [@"\a"];
	print @"""";
	print [@""""];

	print "\n";

	print '\\';
	print ['\\'];
	print "\\";
	print ["\\"];
	print @"\\";
	print [@"\\"];

	print "\n";

	print '0';
	print ['0'];
	print '\0';
	print ['\0'];
	print "\0";
	print ["\0"];
	print @"\0";
	print [@"\0"];

	print "\n";

	print 'n';
	print ['n'];
	print '\n';
	print ['\n'];
	print "\n";
	print ["\n"];
	print @"\n";
	print [@"\n"];

	print "\n";

	print 'r';
	print ['r'];
	print '\r';
	print ['\r'];
	print "\r";
	print ["\r"];
	print @"\r";
	print [@"\r"];

	print "\n";

	print 't';
	print ['t'];
	print '\t';
	print ['\t'];
	print "\t";
	print ["\t"];
	print @"\t";
	print [@"\t"];

	print "\n";
}

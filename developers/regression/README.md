Automated regression test infrastructure for CakeML.

[api.sml](api.sml):
Implements the server-side regression-test API as a CGI program.
The API is for workers to view and manipulate the job queues.

[design.txt](design.txt):
Notes on the design of the automated regression test infrastructure.

[poll.sml](poll.sml):
Implements automatic refreshing of the job queues.
If there are new jobs on GitHub, they will be added to the waiting queue.
If there are stale jobs, they will be removed.

[regressionLib.sml](regressionLib.sml):
Code shared between the pieces of the regression test suite.

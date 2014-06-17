<!DOCTYPE html>
<html>

<head>
  <title>CakeML PP</title>
  <script src="http://cdn.jquerytools.org/1.2.7/full/jquery.tools.min.js"></script>  
  
  <link rel="stylesheet" href="/css/standalone.css"
      type="text/css" media="screen" />
  <link rel="stylesheet" href="/css/tabs.css"
      type="text/css" media="screen" />
  <link rel="stylesheet" href="/css/tabs-panes.css"
      type="text/css" media="screen" />

</head>

<body>

<?php
$descriptorspec = array(
   0 => array("pipe", "r"),  // stdin is a pipe that the child will read from
   1 => array("pipe", "w"),  // stdout is a pipe that the child will write to
   2 => array("file", "/tmp/error-output.txt", "a") // stderr is a file to write to
);

$src = $_GET['src'];
$run = $_GET['run'];

if (isset($src) && isset($run)){
  $process = proc_open('timeout 120s ./runCompile', $descriptorspec, $pipes);
  $src = str_replace(array("\n"), "", $src);
  if(is_resource($process))
  {
    fwrite($pipes[0], $src);
    fclose($pipes[0]);

    $output = stream_get_contents($pipes[1]);
    fclose($pipes[1]);
    $return_value = proc_close($process);
    if($return_value ==124)
       $output = "Compilation timed out";
    $arrs = explode("#@#",$output);
    
    //Remove the first entry and replace |+ with newlines
    //$arrs[7] = str_replace(array("|+"),"\n",$arrs[7]);
    //$arrs[8] = str_replace(array("|+"),"\n",$arrs[8]);

  }
}
?>



<form action="<?php echo($_SERVER['PHP_SELF']); ?>" method="GET">
Code:<br>
<textarea id="prog" rows="24" rows="24" cols="102" name="src"><?php echo $src;?></textarea> <br>
<input type="submit" name="run" value="Compile"/>
</form>
<br>
<br>

<div>

<ul class = "tabs">
	<li><a href="#" class="m">AST</a></li>
	<li><a href="#" class="m">modLang</a></li>
	<li><a href="#" class="m">conLang</a></li>
	<li><a href="#" class="m">decLang</a></li>
	<li><a href="#" class="m">exhLang</a></li>
	<li><a href="#" class="m">patLang</a></li>
	<li><a href="#" class="m">intLang</a></li>
</ul>

<!-- tab "panes" -->
<div class="panes">
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[0];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[1];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[2];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[3];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[4];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[5];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[6];?></textarea>
  </div>
</div>
</div>

<br>

<div>
<ul class = "tabs">
	<li><a href="#" class="m">Globals</a></li>
	<li><a href="#" class="m">Modules</a></li>
	<li><a href="#" class="m">Constructors</a></li>
</ul>
<!-- tab "panes" -->
<div class="panes">
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[7];?></textarea>
  </div>
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[8];?></textarea>
  </div> 
  <div>
    <textarea rows="22" cols="192"><?php echo $arrs[9];?></textarea>
  </div>
</div>
</div>
</body>

<script>
// perform JavaScript after the document is scriptable.
$(function() {
    // setup ul.tabs to work as tabs for each div directly under div.panes
    $("ul.tabs").tabs("div.panes > div");
});
</script>

</html>

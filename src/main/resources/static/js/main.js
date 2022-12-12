// Sistema de uso de formulário via API

var debug = false;

$(document).ready(function(){
  $("main").addClass("container");
});

$( "form" ).submit(function( event ) {
  event.preventDefault();
  
  var formData = new FormData($(this)[ 0 ]);
  var object = {};

  var checkbox = $("form").find("input[type=checkbox]");
  $.each(checkbox, function(key, val) {
	  console.log( $(val).is(':checked'));
      formData.append($(val).attr('name'), $(val).is(':checked'));
  });
  
  formData.forEach((value, key) => object[key] = value);
  
  // trata o JSON cliente ou proprietário
  if(object.hasOwnProperty('cliente'))
  	object['cliente'] =  JSON.parse("{" + object['cliente'] + "}");
  	
  if(object.hasOwnProperty('proprietario'))
  	object['proprietario'] = JSON.parse("{" + object['proprietario'] + "}");
  
  var finalMethod = ($( "form input[name='_method']" ).length) ? 'put' : 'post';
  
  var json = JSON.stringify(object);
  console.log(json);
  
  	$.ajax({
	  url: $( "form" ).attr('action'),
	  type: "post",
	  data: json,
	  contentType:"application/json",
	  dataType:"json",
	  success: function(){
	    var queryStrings = "?successes=Ação realizada com sucesso.";
		if(!debug) window.location.replace($( "form" ).attr('redirect') + queryStrings);
	  },
	  error: function(xhr, status, error) {
	  	  var queryStrings = "?";
	  	  if(window.location.search) queryStrings = "&";
	  	  
		  //var err = eval("(" + xhr.responseText + ")");
		  //if(err.Message == undefined) {
		  	queryStrings += "errors=Não pudemos realizar tal ação. Algo deu errado.";
		  //} else {
		  	// não consegui testar isso ainda
		  	// JSON.parse("{" + err.Message + "}");
		  //}
		  if(!debug) window.location.replace(document.location + queryStrings);
		}
	})
});
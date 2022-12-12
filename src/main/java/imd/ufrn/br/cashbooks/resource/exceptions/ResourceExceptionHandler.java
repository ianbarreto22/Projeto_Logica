package imd.ufrn.br.cashbooks.resource.exceptions;

import java.time.Instant;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.ControllerAdvice;
import org.springframework.web.bind.annotation.ExceptionHandler;
import org.springframework.web.bind.annotation.ResponseBody;

import imd.ufrn.br.cashbooks.service.exceptions.DatabaseException;
import imd.ufrn.br.cashbooks.service.exceptions.ResourceNotFoundException;
import imd.ufrn.br.cashbooks.service.exceptions.ValidationException;

@ControllerAdvice
public class ResourceExceptionHandler {
	
	@ExceptionHandler(ResourceNotFoundException.class)
	public ResponseEntity<StandardError> resourceNotFound(ResourceNotFoundException e, HttpServletRequest request) {
		String error = "Resource not found";
		HttpStatus status = HttpStatus.NOT_FOUND;
		StandardError err = new StandardError(Instant.now(), status.value(), error, e.getMessage(), request.getRequestURI());
		return ResponseEntity.status(status).body(err);
	}
	
	@ExceptionHandler(DatabaseException.class)
	public ResponseEntity<StandardError> database(DatabaseException e, HttpServletRequest request) {
		String error = "Database error";
		HttpStatus status = HttpStatus.BAD_REQUEST;
		StandardError err = new StandardError(Instant.now(), status.value(), error, e.getMessage(), request.getRequestURI());
		return ResponseEntity.status(status).body(err);
	}
	
	@ExceptionHandler(ValidationException.class)
	public ResponseEntity<String> validation(ValidationException e, HttpServletRequest request) throws JSONException {
		String error = "errors";
		HttpStatus status = HttpStatus.UNPROCESSABLE_ENTITY;
		JSONObject err = new JSONObject();
		JSONArray array = new JSONArray();
		JSONObject item = new JSONObject();
		for(Map.Entry<String,String> entry : e.getErrors().entrySet()) {
			item.put(entry.getKey(), entry.getValue());
		}
		array.put(item);
		err.put(error, array);
		System.out.println(err);
		String erro = err.toString();
		return ResponseEntity.status(status).body(erro);		
	}
	
}

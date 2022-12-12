package imd.ufrn.br.cashbooks.resource;

import java.net.URI;
import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.servlet.support.ServletUriComponentsBuilder;

import imd.ufrn.br.cashbooks.model.Cliente;
import imd.ufrn.br.cashbooks.service.ClienteService;

@RestController
@RequestMapping(value = "/api/clientes")
public class ClienteResource {
	
	@Autowired 
	private ClienteService service;
	
	@GetMapping
	public ResponseEntity<List<Cliente>> findAll() {
		List<Cliente> list = service.findAll();
		
		return ResponseEntity.ok().body(list);
	}
	
	@GetMapping(value = "/{id}")
	public ResponseEntity<Cliente> findById(@PathVariable Long id) {
		Cliente obj = service.findById(id);
		return ResponseEntity.ok().body(obj);
	}
	
	@PostMapping(produces=MediaType.APPLICATION_JSON_VALUE)
	public ResponseEntity<Cliente> insert(@RequestBody Cliente obj) {
		obj = service.insert(obj);
		URI uri = ServletUriComponentsBuilder.fromCurrentContextPath().path("/{id}")
				.buildAndExpand(obj.getId()).toUri();
		return ResponseEntity.created(uri).body(obj);
	}
	
	@DeleteMapping(value = "/{id}")
	public ResponseEntity<Void> delete(@PathVariable Long id) {
		service.delete(id);
		return ResponseEntity.noContent().build();
	}
	
	@PutMapping(value = "/{id}")
	public ResponseEntity<Cliente> update (@PathVariable Long id, @RequestBody Cliente obj) {
		obj = service.update(id, obj);
		return ResponseEntity.ok().body(obj);
	}
}

package imd.ufrn.br.cashbooks.resource;

import java.net.URI;
import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
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

import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.service.MovimentacaoService;

@RestController
@RequestMapping(value = "/api/movimentacoes")
public class MovimentacaoResource {
	
	@Autowired 
	private MovimentacaoService service;
	
	@GetMapping
	public ResponseEntity<List<Movimentacao>> findAll() {
		List<Movimentacao> list = service.findAll();
		
		return ResponseEntity.ok().body(list);
	}
	
	@GetMapping(value = "/{id}")
	public ResponseEntity<Movimentacao> findById(@PathVariable Long id) {
		Movimentacao obj = service.findById(id);
		return ResponseEntity.ok().body(obj);
	}
	
	@PostMapping
	public ResponseEntity<Movimentacao> insert(@RequestBody Movimentacao obj) {
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
	public ResponseEntity<Movimentacao> update (@PathVariable Long id, @RequestBody Movimentacao obj) {
		obj = service.update(id, obj);
		return ResponseEntity.ok().body(obj);
	}
	
}

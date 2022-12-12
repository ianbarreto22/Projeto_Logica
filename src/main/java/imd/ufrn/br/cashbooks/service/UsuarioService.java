package imd.ufrn.br.cashbooks.service;

import java.util.List;
import java.util.Optional;

import javax.persistence.EntityNotFoundException;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.dao.EmptyResultDataAccessException;
import org.springframework.stereotype.Service;

import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.repository.UsuarioRepository;
import imd.ufrn.br.cashbooks.service.exceptions.DatabaseException;
import imd.ufrn.br.cashbooks.service.exceptions.ResourceNotFoundException;
import imd.ufrn.br.cashbooks.service.exceptions.ValidationException;

@Service
public class UsuarioService {
	@Autowired
	private /*@ spec_public @*/ UsuarioRepository repository;
	
	/*@ ensures \result == repository.findAll(); @*/
	public /*@ pure @*/ List<Usuario> findAll(){
		return repository.findAll();
	}
	
	/*@ 	public normal_behavior
	  @ 		requires repository.findById(id) != null;
	  @			ensures \result == repository.findById(id);
	  @	also
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException;@*/
	public /*@ pure @*/ Usuario findById(Long id) {
		Optional<Usuario> obj = repository.findById(id);

        return obj.orElseThrow(() -> new ResourceNotFoundException(id));
	}
	
	/*@ 	public normal_behavior
	  @ 		requires repository.findByEmail(email) != null;
	  @			ensures \result == repository.findByEmail(email);
	  @	also
	  @		public exceptional_behavior
	  @			requires repository.findByEmail(email) == null;
	  @			signals_only ResourceNotFoundException;@*/
	public /*@ pure @*/ Usuario findByEmail(String email) {
		Optional<Usuario> obj = repository.findByEmail(email);
		
		return obj.orElseThrow(() -> new ResourceNotFoundException(email));
	}
	
	/*@ 	public normal_behavior 
	  @ 		requires obj != null && obj.getNome() != null;
	  @	 		requires obj.getEmail != null && obj.getNomeComercio() != null;
	  @			requires obj.getCnpj() != null && CNPJService.validaCNPJ(obj.getCnpj());
	  @			ensures repository.findAll().size() == \old(repository.findAll().size()+1);
	  @ also
	  @		public exceptional_behavior
	  @			requires obj.getNome() == null;
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getEmail() == null;
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getCnpj() == null && !(CNPJService.validaCNPJ(obj.getCnpj()));
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getNomeComercio() == null;
	  @			signals_only ValidationException;@*/
	public /*@ pure @*/ Usuario insert(Usuario obj) {
		ValidationException exception = new ValidationException("errors");
		
		if(obj.getNome() == null) {
			exception.addError("nome", "Campo vazio");
		}
		
		
		if(obj.getEmail() == null) {
			exception.addError("e-mail", "Campo vazio");
		}
		
		if(obj.getCnpj() == null ) {
			exception.addError("cnpj", "Campo vazio");		
		} else if(!CNPJService.validaCNPJ(obj.getCnpj())) {
			exception.addError("cnpj", "Valor inválido");
		}
		
		
		if(obj.getNomeComercio() == null) {
			exception.addError("nome comércio", "Campo vazio");
		}
		
		if(exception.getErrors().size() > 0) {
			throw exception;
		}
		
        return repository.save(obj);
    }
	
	/*@ 	public normal_behavior
	  @			requires repository.findById(id) != null;
	  @			ensures repository.findAll().size() == \old(repository.findAll().size()-1)
	  @	also
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException@*/
	public /*@ pure @*/ void delete(Long id) {
        try {
            repository.deleteById(id);
        } catch (EmptyResultDataAccessException e) {
        	throw new ResourceNotFoundException(id);
        } catch (DataIntegrityViolationException e) {
        	throw new DatabaseException(e.getMessage());
        }
    }
	
	/*@		 public normal_behavior
	  @			requires repository.findById(id) != null && obj != null;
	  @			ensures repository.findById(id).equals(obj);
	  @	also
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException;@*/
	public /*@ pure @*/ Usuario update(Long id, Usuario obj) {
		Usuario entity = null;
		try {
            entity = repository.getById(id);
            updateData(entity, obj);
            return repository.save(entity);
        } catch(EntityNotFoundException e) {
        	throw new ResourceNotFoundException(id);
        }
    }

	/*@ 	public normal_behavior
	  @			requires entity != null && obj != null;
	  @			requires obj.getNome() != null && obj.getEmail() != null;
	  @			requires obj.getCnpj() != null && CNPJService.validaCNPJ(obj.getCnpj());
	  @			requires obj.getNomeComercio() != null;
	  @			ensures entity.equals(obj);
	  @ also
	  @		public exceptional_behavior
	  @			requires obj.getNome() == null;
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getEmail() == null;
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getCnpj() == null;
	  @			signals_only ValidationException;
	  @		also
	  @			requires !(CNPJService.validaCNPJ(obj.getCnpj()));
	  @			signals_only ValidationException;
	  @		also
	  @			requires obj.getNomeComercio() == null;
	  @			signals_only ValidationException;@*/
	private /*@ pure @*/ void updateData(Usuario entity, Usuario obj) {
		ValidationException exception = new ValidationException("errors");
		
		if(obj.getNome() == null) {
			exception.addError("nome", "Campo vazio");
		}
		
		
		if(obj.getEmail() == null) {
			exception.addError("e-mail", "Campo vazio");
		}
		
		if(obj.getCnpj() == null ) {
			exception.addError("cnpj", "Campo vazio");		
		} else if(!CNPJService.validaCNPJ(obj.getCnpj())) {
			exception.addError("cnpj", "Valor inválido");
		}
		
		
		if(obj.getNomeComercio() == null) {
			exception.addError("nome comércio", "Campo vazio");
		}
		
		if(exception.getErrors().size() > 0) {
			throw exception;
		}
				
		entity.setNome(obj.getNome());
		entity.setEmail(obj.getEmail());
		entity.setCnpj(obj.getCnpj());		
		entity.setNomeComercio(obj.getNomeComercio());
		entity.setCor(obj.getCor());

	}
	
	/*@ ensures \result == findById(1L); @*/
	public Usuario getUsuario() {
		Usuario usuario;
		try {
			usuario = findById(1L);
		}
		catch(ResourceNotFoundException e) {
			usuario = new Usuario();
			repository.save(usuario);
		}
		
		return usuario;
	}
}

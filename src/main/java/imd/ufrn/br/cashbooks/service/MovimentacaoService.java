package imd.ufrn.br.cashbooks.service;



import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import javax.persistence.EntityNotFoundException;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.dao.EmptyResultDataAccessException;
import org.springframework.stereotype.Service;

import imd.ufrn.br.cashbooks.extensions.CategorizarPequenosComerciantes;
import imd.ufrn.br.cashbooks.extensions.RegraPequenosComerciantes;
import imd.ufrn.br.cashbooks.extensions.RelatorioCSV;
import imd.ufrn.br.cashbooks.interfaces.ICategorizarAutomaticamente;
import imd.ufrn.br.cashbooks.interfaces.IGerarRelatorio;
import imd.ufrn.br.cashbooks.interfaces.IRestricoesComprasPrazo;
import imd.ufrn.br.cashbooks.model.Cliente;
import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.model.enums.MovimentacaoStatus;
import imd.ufrn.br.cashbooks.repository.MovimentacaoRepository;
import imd.ufrn.br.cashbooks.repository.UsuarioRepository;
import imd.ufrn.br.cashbooks.service.exceptions.DatabaseException;
import imd.ufrn.br.cashbooks.service.exceptions.ResourceNotFoundException;
import imd.ufrn.br.cashbooks.service.exceptions.ValidationException;

@Service
public class MovimentacaoService {
	
	@Autowired
	private /*@ spec_public @*/ MovimentacaoRepository repository;
	
	@Autowired
	private ClienteService serviceCliente;
	
	@Autowired 
	private UsuarioService serviceUsuario;
	
	
	@Autowired
	private UsuarioRepository proprietarioRepository;
	
	private /*@ spec_public @*/ ICategorizarAutomaticamente categoriaStrategy;
	
	private /*@ spec_public @*/ IGerarRelatorio relatorioStategy;
	
	private /*@ spec_public @*/ IRestricoesComprasPrazo prazoStrategy;
	
	@Autowired
	private RegraPequenosComerciantes regra;
	
	/*@ requires strategy != null;
	  @ assignable categoriaStrategy;
	  @ ensures relatorioStrategy == strategy; @*/
	public void setCategoriaStrategy (ICategorizarAutomaticamente strategy) {
		this.categoriaStrategy = strategy;
	}
	
	public /*@ pure @*/ String getRelatorio() {
		if(relatorioStategy == null) this.setRelatorioStrategy(new RelatorioCSV());
			
		return relatorioStategy.gerarRelatorio(this.findAll());
	}
	
	/*@ requires mov != null;
	  @ ensures mov.getCategoria != \old(mov.getCategoria());	
		@*/
	public /*@ pure @*/ void categorizar(Movimentacao mov) {
		categoriaStrategy.categorizar(mov);
	}
	
	/*@ requires mov != null;
	  @ ensures \result == prazoStrategy.validarMovimentacao(mov);@*/
	public /*@ pure @*/ boolean validarMovimentacao(Movimentacao mov) {
		return prazoStrategy.validarMovimentacao(mov);
	}
	
	/*@ requires strategy != null;
	  @ assignable relatorioStrategy;
	  @ ensures relatorioStrategy == strategy; @*/
	public void setRelatorioStrategy(IGerarRelatorio strategy) {
		this.relatorioStategy = strategy;
	}
	
	/*@ requires strategy != null;
	  @ assignable prazoStrategy;
	  @ ensures prazoStrategy == strategy; @*/
	public void setPrazoStrategy(IRestricoesComprasPrazo strategy) {
		this.prazoStrategy = strategy;
	}
	
	/*@ ensures \result == repository.findAll();@*/
	public /*@ pure @*/ List<Movimentacao> findAll(){
		return repository.findAll();
	}
	
	/*@ 	public normal_behavior
	  @ 		requires repository.findById(id) != null;
	  @			ensures \result == repository.findById(id);
	  @ also	
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException; @*/
	public /*@ pure @*/ Movimentacao findById(Long id) {
		Optional<Movimentacao> obj = repository.findById(id);

        return obj.orElseThrow(() -> new ResourceNotFoundException(id));
	}
	
	
	/*@ 	public normal_behavior
	  @			requires obj != null && obj.getDescricao() != null;
	  @			requires obj.getDataCobranca() != null && obj.getDataMovimentacao() != null;
	  @			requires obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @         requires obj.getStatus() != null && obj.getValor() != null;
	  @			requires obj.getStatus() == MovimentacaoStatus.ENTRADA;
	  @ 		ensures obj.getCategoria != /old(obj.getCategoria());
	  @         ensures serviceUsuario.getUsuario().getSaldo() == \old(serviceUsuario.getUsuario().getSaldo()+obj.getValor());
	  @			ensures repository.findAll.size() == \old(repository.findAll().size()+1);
	  @		also
	  @			requires obj.getDataCobranca() != null && obj.getDataMovimentacao() != null;
	  @			requires obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @         requires obj.getStatus() != null && obj.getValor() != null;
	  @			requires obj.getStatus() == MovimentacaoStatus.SAIDA;
	  @ 		ensures obj.getCategoria != /old(obj.getCategoria()); 		
	  @			ensures serviceUsuario.getUsuario().getSaldo() == \old(serviceUsuario.getUsuario().getSaldo()-obj.getValor());
	  @         ensures repository.findAll.size() == \old(repository.findAll().size()+1);
	  @ also	
	  @		 public exceptional_behavior
	  @			requires obj == null;
	  @         signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDescricao() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDataCobranca() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDataMovimentacao == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires !obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getStatus() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getValor() == null;
	  @			signals_only ValidationException;
	  @ 	
												@*/
	public /*@ pure @*/Movimentacao insert(Movimentacao obj) {		
		//Optional<Usuario> op = proprietarioRepository.findById(1L);
		//Usuario prop = op.get();
		Usuario prop = serviceUsuario.getUsuario();
		
		setCategoriaStrategy(new CategorizarPequenosComerciantes());
		setPrazoStrategy(regra);
		
		
		ValidationException exception = new ValidationException("errors");
		
		if(obj.getCliente().getId() == null) {//Movimentação sem cliente
			obj.setCliente(null);
		}
		
		if(obj.getDataCobranca() == null) {
			exception.addError("dataCobranca", "campo vazio");
		}
		
		if(obj.getDataMovimentacao() == null) {
			exception.addError("dataMovimentacao", "campo vazio");
		}
		
		if(obj.getDataCobranca() != null && obj.getDataMovimentacao() != null) {
			if(obj.getDataCobranca().isBefore(obj.getDataMovimentacao())) {
				exception.addError("datas", "A data de cobranca não pode ser anterior a data de movimentacao");
			}
		}
		
		if(obj.getDescricao() == null) {
			exception.addError("descricao", "campo vazio");
		}
		
		if(obj.getStatus() == null) {
			exception.addError("status", "campo vazio");
		}
		
		if(obj.getValor() == null) {
			exception.addError("valor", "campo vazio");
		}

		if(!validarMovimentacao(obj)) {
			exception.addError("prazo", "movimentacao invalida");
		}
		
		if(exception.getErrors().size() > 0) {
			throw exception;
		}
		
		
		if(obj.getStatus() == MovimentacaoStatus.ENTRADA) {
			prop.setSaldo(prop.getSaldo() + obj.getValor());
        } else if(obj.getStatus() == MovimentacaoStatus.SAIDA){
			prop.setSaldo(prop.getSaldo() - obj.getValor());
        }
		
		categorizar(obj);
		
		Movimentacao mov = repository.save(obj);
		
        return mov;
    }
	/*@ 	public normal_behavior
	  @			requires repository.findById(id) != null;
	  @			ensures repository.findAll().size() == \old(repository.findAll().size()-1)	
	  @ also
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException
	  @*/
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
	  @			signals_only ResourceNotFoundException;
	  @*/
	public /*@ pure @*/ Movimentacao update(Long id, Movimentacao obj) {
		Movimentacao entity = null;
		try {
            entity = repository.getById(id);
            updateData(entity, obj);
            return repository.save(entity);
        } catch(EntityNotFoundException e) {
            throw new ResourceNotFoundException(id);
        }
    }
	
	/*@ 	public normal_behavior
	  @			requires obj != null && obj.getDescricao() != null;
	  @			requires obj.getDataCobranca() != null && obj.getDataMovimentacao() != null;
	  @			requires obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @         requires obj.getStatus() != null && obj.getValor() != null;
	  @			requires obj.getStatus() == MovimentacaoStatus.ENTRADA;
	  @ 		ensures obj.getCategoria != /old(obj.getCategoria());
	  @         ensures serviceUsuario.getUsuario().getSaldo() == \old(serviceUsuario.getUsuario().getSaldo()+obj.getValor());
	  @			ensures repository.findAll.size() == \old(repository.findAll().size());
	  @		also
	  @			requires obj.getDataCobranca() != null && obj.getDataMovimentacao() != null;
	  @			requires obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @         requires obj.getStatus() != null && obj.getValor() != null;
	  @			requires obj.getStatus() == MovimentacaoStatus.SAIDA;
	  @ 		ensures obj.getCategoria != /old(obj.getCategoria()); 		
	  @			ensures serviceUsuario.getUsuario().getSaldo() == \old(serviceUsuario.getUsuario().getSaldo()-obj.getValor());
	  @         ensures repository.findAll.size() == \old(repository.findAll().size());
	  @ also	
	  @		 public exceptional_behavior
	  @			requires obj == null;
	  @         signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDescricao() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDataCobranca() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getDataMovimentacao == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires !obj.getDataCobranca().isBefore(obj.getDataMovimentacao());
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getStatus() == null;
	  @			signals_only ValidationException;
	  @		 also	
	  @			requires obj.getValor() == null;
	  @			signals_only ValidationException;
	  @ 	
	  @*/
	private /*@ pure @*/ void updateData(Movimentacao entity, Movimentacao obj) {
	
		ValidationException exception = new ValidationException("errors");
		
		if(obj.getCliente() == null) {//Movimentação sem cliente
			obj.setCliente(null);
		}
		
		if(obj.getDataCobranca() == null) {
			exception.addError("dataCobranca", "campo vazio");
		}
		
		if(obj.getDataMovimentacao() == null) {
			exception.addError("dataMovimentacao", "campo vazio");
		}
		
		if(obj.getDataCobranca() != null && obj.getDataMovimentacao() != null) {
			if(obj.getDataCobranca().isBefore(obj.getDataMovimentacao())) {
				exception.addError("datas", "A data de cobranca não pode ser anterior a data de movimentacao");
			}
		}
		
		if(obj.getDescricao() == null) {
			exception.addError("descricao", "campo vazio");
		}
		
		if(obj.getStatus() == null) {
			exception.addError("status", "campo vazio");
		}
		
		if(obj.getValor() == null) {
			exception.addError("valor", "campo vazio");
		}
		
		if(!validarMovimentacao(obj)) {
			exception.addError("prazo", "movimentacao invalida");
		}
		
		if(exception.getErrors().size() > 0) {
			throw exception;
		}
		
		categorizar(obj);
				
		entity.setDataCobranca(obj.getDataCobranca());
		entity.setValor(obj.getValor());
		entity.setDescricao(obj.getDescricao());
		entity.setCliente(obj.getCliente());
		entity.setStatus(obj.getStatus());
		
	}
	
	/*@ ensures \result == getBalancoDoDia(LocalDate.now());@*/ 
	public /*@ pure @*/ Double getBalancoDiario() {	
		return getBalancoDoDia(LocalDate.now());
	}
	
	/*@ requires diasAver > 0;
	  @ ensures \result != null;  
	@*/
	public /*@ pure @*/ List<Double> getBalancoRetroativamente(int diasAVer) {
		List<Double> saldos = new ArrayList<>();

		for(LocalDate date = LocalDate.now().minusDays(diasAVer); date.isBefore(LocalDate.now()) || date.isEqual(LocalDate.now()); date = date.plusDays(1)) {
			saldos.add(getBalancoDoDia(date));
		}
		
		return saldos;
	}
	
	/*@ requires data != null;
	  @ ensures \result != null;
	@*/
	public /*@ pure @*/ Double getBalancoDoDia(LocalDate data) {

		List<Movimentacao> movimentacoes = repository.findAllByDataMovimentacao(data);
		Double saldo = 0.0;
		
		for(Movimentacao mov : movimentacoes) {
			if(mov.getStatus() == MovimentacaoStatus.ENTRADA && mov.getDataMovimentacao().isEqual(mov.getDataCobranca()))
				saldo += mov.getValor();
	        else if (mov.getStatus() == MovimentacaoStatus.SAIDA && mov.getDataMovimentacao().isEqual(mov.getDataCobranca()))
	        	saldo -= mov.getValor();
		
		}
		
		return saldo;
	}
	
	/*@ ensures \result != null; @*/
	public /*@ pure @*/ List<Movimentacao> getMovimentacoesFiadoHoje() {
		
		
		LocalDate dataLocal = LocalDate.now();
		

		List<Movimentacao> movimentacoes = repository.findAllByDataCobranca(dataLocal);
		List<Movimentacao> movimentacoesFiado = new ArrayList<Movimentacao>();
		
		for(Movimentacao mov : movimentacoes) {
			if(!mov.isPago()) {
				movimentacoesFiado.add(mov);
			}
		}
		
		return movimentacoesFiado;
	}
	
	/*@ ensures \result != null; @*/
	public /*@ pure @*/ List<Movimentacao> getMovimentacoesFiado(){
		
		List<Movimentacao> movimentacoes = repository.findAll();
		List<Movimentacao> movimentacoesFiado = new ArrayList<Movimentacao>();
		
		for(Movimentacao mov : movimentacoes) {
			if(!mov.isPago()) {
				movimentacoesFiado.add(mov);
			}
		}
		
		return movimentacoesFiado;
	}
	
	/*@ ensures \result == repository.findAllByCliente(cliente); @*/
	public /*@ pure @*/ List<Movimentacao>findAllByCliente(Cliente cliente){
		return repository.findAllByCliente(cliente);
	}
	
	/*@ 	public normal_behavior 
	  @ 		requires repository.findById(id) != null;
	  @			ensures repository.findById(id).isPago();
	  @ also
	  @		public exceptional_behavior
	  @			requires repository.findById(id) == null;
	  @			signals_only ResourceNotFoundException;@*/
	public /*@ pure @*/ Movimentacao pagarMovimentacao(Long id) {
		Movimentacao mov = findById(id);
		
		mov.setPago(true);
		update(id, mov);
		
		return mov;
	}
	
	/*@ ensures \result != null;@*/
	public /*@ pure @*/ List<Movimentacao> getDividas(){
		List<Movimentacao> movimentacoesSaida = repository.findAll();
		List<Movimentacao> movimentacoesDivida = new ArrayList();
		
		for(Movimentacao mov : movimentacoesSaida) {
			if((!mov.isPago()) && mov.getStatus() == MovimentacaoStatus.SAIDA) {
				movimentacoesDivida.add(mov);
			}
		}
		
		return movimentacoesDivida;
	}
	
}
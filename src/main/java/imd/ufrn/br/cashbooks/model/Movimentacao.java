package imd.ufrn.br.cashbooks.model;

import java.io.Serializable;
import java.time.LocalDate;

import javax.persistence.CascadeType;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.JoinColumn;
import javax.persistence.ManyToOne;
import javax.persistence.Table;


import imd.ufrn.br.cashbooks.model.enums.Categoria;
import imd.ufrn.br.cashbooks.model.enums.MovimentacaoStatus;

@Entity
@Table(name = "tb_movimentacao")
public class Movimentacao implements Serializable {

	private static final long serialVersionUID = 1L;
	
	@Id
	@GeneratedValue (strategy = GenerationType.IDENTITY)
	private /*@ spec_public @*/ Long id;
	
	private /*@ spec_public @*/ LocalDate dataCobranca;
	private /*@ spec_public @*/ LocalDate dataMovimentacao;
	
	private  /*@ spec_public @*/ boolean pago;


	private /*@ spec_public @*/ Integer status;
	private /*@ spec_public @*/ Integer categoria = 0;
	private /*@ spec_public @*/ Double valor;
	private /*@ spec_public @*/ String descricao;
	
	@ManyToOne
	@JoinColumn(name = "cliente_id")
	private /*@ spec_public @*/ Cliente cliente;
	
	@ManyToOne
	@JoinColumn(name = "usuario_id")
	private /*@ spec_public @*/ Usuario usuario;

	public Movimentacao() {
		
	}	
	
	/*@ assignable id, dataCobranca, dataMovimentacao, status, categoria, valor, descricao, cliente, usuario;
	  @ ensures this.id == id;
	  @ ensures this.dataCobranca == dataCobranca;
	  @ ensures this.dataMovimentacao == dataMovimentacao;
	  @ ensures this.status == status;
	  @ ensures this.categoria == categoria;
	  @ ensures this.valor == valor;
	  @ ensures this.descricao == descricao;
	  @ ensures this.cliente == cliente;
	  @ ensures this.usuario == usuario;
	@*/
	public Movimentacao(Long id, LocalDate dataCobranca, LocalDate dataMovimentacao, Integer status, Integer categoria, Double valor,
			String descricao, Cliente cliente, Usuario usuario) {
		super();
		this.id = id;
		this.dataCobranca = dataCobranca;
		this.dataMovimentacao = dataMovimentacao;
		this.status = status;
		this.categoria = categoria;
		this.valor = valor;
		this.descricao = descricao;
		this.cliente = cliente;
		this.usuario = usuario;
	}

	public Long getId() {
		return id;
	}
	
	/*@ requires id!= null && id > 0;
	  @	assignable id;
	  @ ensures this.id == id;
	@*/
	public void setId(Long id) {
		this.id = id;
	}
	
	public boolean isPago() {
		return pago;
	}
	
	
	public void setPago(boolean pago) {
		this.pago = pago;
	}
	
	public Usuario getUsuario() {
		return usuario;
	}
	
	/*@ requires usuario != null;
	  @ assignable usuario;
	  @ ensures this.usuario == usuario;@*/
	public void setUsuario(Usuario usuario) {
		this.usuario = usuario;
	}


	public MovimentacaoStatus getStatus() {
		if(this.status == null) return null;
		else return MovimentacaoStatus.valueOf(this.status);
	}
	
	/*@ requires movimentacaoStatus != null;
	  @ assignable status;
	  @ ensures this.status == movimentacaoStatus; @*/
	public void setStatus(MovimentacaoStatus movimentacaoStatus) {
		if(movimentacaoStatus != null) {
			this.status = movimentacaoStatus.getCode();
		}
	}
	
	public Categoria getCategoria() {
		if(this.categoria == null) return null;
		else return Categoria.valueOf(this.categoria);
	}
	
	/*@ requires categoria != null;
	  @ assignable categoria;
	  @ ensures this.categoria == categoria; @*/
	public void setCategoria(Categoria categoria) {
		if(categoria != null) {
			this.categoria = categoria.getCode();
		}
	}

	public Double getValor() {
		return valor;
	}
	
	/*@ requires valor != null && valor >= 0;
	  @ assignable valor;
	  @ ensures this.valor == valor; @*/
	public void setValor(Double valor) {
		this.valor = valor;
	}

	public String getDescricao() {
		return descricao;
	}
	
	/*@ requires descricao != null;
	  @ assignable descricao;
	  @ ensures this.descricao == descricao; @*/
	public void setDescricao(String descricao) {
		this.descricao = descricao;
	}

	public Cliente getCliente() {
		return cliente;
	}
	
	/*@ requires cliente != null;
	  @ assignable cliente;
	  @ ensures this.cliente == cliente; @*/
	public void setCliente(Cliente cliente) {
		this.cliente = cliente;
	}

	
	public LocalDate getDataCobranca() {
		return dataCobranca;
	}
	
	/*@ requires dataCobranca != null;
	  @ assignable dataCobranca;
	  @ ensures this.dataCobranca == dataCobranca; @*/
	public void setDataCobranca(LocalDate dataCobranca) {
		this.dataCobranca = dataCobranca;
	}

	public LocalDate getDataMovimentacao() {
		return dataMovimentacao;
	}
	
	/*@ requires dataMovimentacao != null;
	  @ assignable dataMovimentacao;
	  @ ensures this.dataMovimentacao == dataMovimentacao; @*/
	public void setDataMovimentacao(LocalDate dataMovimentacao) {
		this.dataMovimentacao = dataMovimentacao;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (id ^ (id >>> 32));
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Movimentacao other = (Movimentacao) obj;
		if (id != other.id)
			return false;
		return true;
	}
}

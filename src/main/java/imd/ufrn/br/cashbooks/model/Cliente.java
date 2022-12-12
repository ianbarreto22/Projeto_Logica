package imd.ufrn.br.cashbooks.model;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.InputMismatchException;
import java.util.List;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.OneToMany;

import com.fasterxml.jackson.annotation.JsonIgnore;

@Entity
public class Cliente implements Serializable {

	private static final long serialVersionUID = 1L;
	
	@Id
	@GeneratedValue (strategy = GenerationType.IDENTITY)
	protected /*@ spec_public non_null @*/ Long id;
	
	private /*@ spec_public non_null @*/ double divida;
	//@ public invariant 0 <= divida;
	
	private /*@ spec_public non_null @*/ String nome;
	private /*@ spec_public non_null @*/ String email;
	private /*@ spec_public non_null @*/ String cpf;
	private /*@ spec_public non_null @*/ String telefone;
	private /*@ spec_public non_null @*/ String endereco;
	
	@JsonIgnore
	@OneToMany(mappedBy = "cliente")
	private List<Movimentacao> movimentacoes = new ArrayList<>();
	//@ public initially movimentacoes.size() == 0;
	
	/*@ assignable divida;
	  @ ensures divida == 0; @*/
	public Cliente() {
		divida=0;
	}
	
	/*@ requires saldo >= 0;
	  @ assignable id, divida, nome, email, cpf, telefone, endereco;
	  @ ensures this.id == id;
	  @ ensures this.divida == divida;
	  @ ensures this.nome == nome;
	  @ ensures this.email == email;
	  @ ensures this.cpf == cpf;
	  @ ensures this.telefone == telefone;
	  @ ensures this.endereco == endereco;@*/
	public Cliente(Long id, double saldo, String nome, String email, String cpf, String telefone, String endereco) {
		this.id = id;
		this.divida = saldo;
		this.nome = nome;
		this.email = email;
		this.cpf = cpf;
		this.telefone = telefone;
		this.endereco = endereco;
	}

	public /*@ pure @*/ String getCpf() {
		return cpf;
	}
	
	/*@ requires cpf != null && cpf.length() == 14;
	  @ assignable cpf;
	  @ ensures this.cpf == cpf;@*/
	public void setCpf(String cpf) {
		this.cpf = cpf;
	}
	
	/*@ requires cpf != null && cpf.length() == 14;
	  @ assignable cpf;
	  @ ensures this.cpf == cpf;@*/
	public /*@ pure @*/ String getTelefone() {
		return telefone;
	}
	
	/*@ requires telefone != null && telefone.length() == 15;
	  @ assignable telefone;
	  @ ensures this.telefone == telefone;@*/
	public void setTelefone(String telefone) {
		this.telefone = telefone;
	}
	
	public /*@ pure @*/ String getEndereco() {
		return endereco;
	}
	
	/*@ requires endereco != null && endereco.length() > 0;
	  @ assignable endereco;
	  @ ensures this.endereco == endereco;@*/
	public void setEndereco(String endereco) {
		this.endereco = endereco;
	}

	public List<Movimentacao> getMovimentacoes() {
		return movimentacoes;
	}
	
	public Long getId() {
		return id;
	}

	/*@ requires id != null && id > 0;
	  @ assignable id;
	  @ ensures this.id == id;@*/
	public void setId(Long id) {
		this.id = id;
	}

	public String getNome() {
		return nome;
	}

	/*@ requires nome != null && nome.length() > 0;
	  @ assignable nome;
	  @ ensures this.nome == nome;@*/
	public void setNome(String nome) {
		this.nome = nome;
	}

	public String getEmail() {
		return email;
	}

	/*@ requires email != null && email.length() > 0;
	  @ assignable email;
	  @ ensures this.endereco == endereco;@*/
	public void setEmail(String email) {
		this.email = email;
	}

	public double getDivida() {
		return divida;
	}

	/*@ requires divida > 0;
	  @ assignable divida;
	  @ ensures this.divida == divida;@*/
	public void setDivida(double divida) {
		this.divida = divida;
	}

	public static long getSerialversionuid() {
		return serialVersionUID;
	}

	
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (this.id ^ (this.id >>> 32));
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
		Cliente other = (Cliente) obj;
		if (id != other.id)
			return false;
		return true;
	}
}
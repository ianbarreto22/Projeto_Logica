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
public class Usuario implements Serializable {

	private static final long serialVersionUID = 1L;
	
	@Id
	@GeneratedValue (strategy = GenerationType.IDENTITY)
	private /*@ spec_public @*/ Long id;
	
	private /*@ spec_public @*/ String nome;
	
	private /*@ spec_public @*/ String email;
	private /*@ spec_public @*/ double saldo;
	//TODO private String senha;
	

	private /*@ spec_public @*/ String cnpj;

	// Variáveis de configuração do site, para customizar da forma que o comerciante
	// bem desejar
	private /*@ spec_public @*/ String nomeComercio="NOME DA EMPRESA";
	//@ public initially nomeComercio = "NOME DA EMPRESA";

	private /*@ spec_public @*/ String cor="#ff0000";
	//@ public initially cor = "#ff0000";
	

	@JsonIgnore
	@OneToMany(mappedBy = "usuario")
	private List<Movimentacao> movimentacoes = new ArrayList<>();
	//@ public initially movimentacoes.size() == 0;
	
	/*@ assignable id, nome, email, saldo, cnpj, nomeComercio, cor;
	  @ ensures this.id == id;
	  @ ensures this.nome == nome;
	  @ ensures this.email == email;
	  @ ensures this.saldo == saldo;
	  @ ensures this.cnpj == cnpj;
	  @ ensures this.nomeComercio == nomeComercio;
	  @ ensures this.cor == cor;@*/
	public Usuario(Long id, String nome, String email, double saldo, String cnpj, String nomeComercio,
			String cor) {
		this.id = id;
		this.nome = nome;
		this.email = email;
		this.saldo = saldo;
		this.cnpj = cnpj;
		this.nomeComercio = nomeComercio;
		this.cor = cor;
	}

	public Usuario() {
		
	}
	
	public List<Movimentacao> getMovimentacoes() {
		return movimentacoes;
	}


	public Long getId() {
		return id;
	}

	/*@ requires id!= null && id > 0;
	  @	assignable id;
	  @ ensures this.id == id; @*/
	public void setId(Long id) {
		this.id = id;
	}


	public String getNome() {
		return nome;
	}

	/*@ requires nome != null && nome.length() > 0;
	  @	assignable nome;
	  @ ensures this.nome == nome; @*/
	public void setNome(String nome) {
		this.nome = nome;
	}


	public String getEmail() {
		return email;
	}

	/*@ requires email != null && email.length() > 0;
	  @	assignable email;
	  @ ensures this.email == email; @*/
	public void setEmail(String email) {
		this.email = email;
	}


	public double getSaldo() {
		return saldo;
	}

	/*@ requires saldo != null;
	  @	assignable saldo;
	  @ ensures this.saldo == saldo; @*/
	public void setSaldo(double saldo) {
		this.saldo = saldo;
	}


	public String getCnpj() {
		return cnpj;
	}
	
	/*@ requires cnpj != null && cnpj.length() == 18;
	  @	assignable cnpj;
	  @ ensures this.cnpj == cnpj; @*/
	public void setCnpj(String cnpj) {			
		this.cnpj = cnpj;
	}

	public String getNomeComercio() {
		return nomeComercio;
	}

	/*@ requires nomeComercio != null && nomeComercio.length() > 0;
	  @	assignable nomeComercio;
	  @ ensures this.nomeComercio == nomeComercio; @*/
	public void setNomeComercio(String nomeComercio) {
		this.nomeComercio = nomeComercio;
	}

	public String getCor() {
		return cor;
	}

	/*@ requires cor != null;
	  @	assignable cor;
	  @ ensures this.cor == cor; @*/
	public void setCor(String cor) {		
		this.cor = cor;
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
		Usuario other = (Usuario) obj;
		if (id != other.getId())
			return false;
		return true;
	}
}
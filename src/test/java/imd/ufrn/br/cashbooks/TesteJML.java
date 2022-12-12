package imd.ufrn.br.cashbooks;

import imd.ufrn.br.cashbooks.service.ClienteService;

public class TesteJML {
	
	//@ requires a == 0;
	//@ ensures \result == true;
	public /*@ pure @*/ boolean teste(int a) {
		return a == 0;
	}
	
	public static void main(String args[]) {
		TesteJML teste = new TesteJML();
		teste.teste(1);
	}
}

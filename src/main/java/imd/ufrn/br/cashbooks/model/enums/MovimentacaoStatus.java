package imd.ufrn.br.cashbooks.model.enums;

import java.util.Arrays;

public enum MovimentacaoStatus {
	ENTRADA(1),
	SAIDA(2);
	
	private int code;
	
	private MovimentacaoStatus(int code) {
		this.code = code;
	}
	
	public int getCode() {
		return code;
	}
	
	public static MovimentacaoStatus valueOf(int code) {
		for(MovimentacaoStatus value : MovimentacaoStatus.values()) {
			if(value.getCode() == code) {
				return value;
			}
		}
		
		throw new IllegalArgumentException("Invalid Movimentacao Status code");
	}
}

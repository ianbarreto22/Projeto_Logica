package imd.ufrn.br.cashbooks.model.enums;

public enum Categoria {
	ROUBO(1),
	ESTOQUE(2),
	CAIXA(3),
	DESPESAS_DIVERSAS(4);
	
	private int code;
	
	private Categoria(int code) {
		this.code = code;
	}
	
	public int getCode() {
		return code;
	}
	
	public static Categoria valueOf(int code) {
		for(Categoria value : Categoria.values()) {
			if(value.getCode() == code) {
				return value;
			}
		}
		
		throw new IllegalArgumentException("Invalid Categoria code");
	}
}
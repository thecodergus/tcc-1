module pow {
    // Define o tipo Node como uma string (identificador de nó)
    type Node = str

    // Definindo uma variante para miner_id que pode ser "first" ou um Node
    type MinerId =
        | First       // Representa o bloco inicial, valor especial
        | Miner(Node) // Representa o minerador por um Node

    // Tipo Block, onde miner_id agora usa a variante MinerId
    type Block = {
        miner_id: MinerId,       // "First" ou um Node encapsulado em Miner
        block_id: int,           // Deve estar no intervalo 0..3
        prev_block_id: int       // Deve estar no intervalo -1..3
    }

    // Conjunto de blocos (blcks) e propriedades na cadeia (definindo tipos de cada variável do estado)
    var blcks: Set[Block]                        // Conjunto de blocos válidos
    var chain: Node -> Set[Block]                // Cada nó aponta para um subconjunto de blocos
    var last_block_id: Node -> int               // Inteiro representando o ID do último bloco, valores entre 0 e 3
    var status: Node -> str                      // Estado do nó, valores "mined" ou "miner"
    var status_changer: Node -> int              // Indicador de mudança de status, valores 0 ou 1
}

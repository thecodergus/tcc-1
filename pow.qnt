module pow {
    // Define o tipo Node como uma string (identificador de nó)
    type Node = str

    // Definindo uma variante para miner_id que pode ser "first" ou um Node
    type MinerId =
        | First       // Representa o bloco inicial, valor especial
        | Node

    // Enumeradores para o estado do minerador
    type MinerStatus =
        | MINED
        | MINER

    // Tipo Block, onde miner_id agora usa a variante MinerId
    type Block = {
        miner_id: MinerId,       // "First" ou um Node encapsulado em Miner
        block_id: int,           // Deve estar no intervalo 0..3
        prev_block_id: int       // Deve estar no intervalo -1..3
    }

    // Variáveis de estado que representam os blocos e as propriedades na cadeia
    const nodes: Set[Node]                    // Conjunto de nós mineradores
    var blcks: Set[Block]                     // Conjunto de blocos válidos
    var chain: Node -> Set[Block]             // Cada nó aponta para um subconjunto de blocos
    var last_block_id: Node -> int            // Último bloco minerado por cada nó (0 a 3)
    var status: Node -> MinerStatus           // Estado do nó, valores MINED ou MINER
    var status_changer: Node -> int           // Indicador de mudança de status, valores 0 ou 1

    // Função para verificar se um bloco é válido conforme as restrições definidas
    def isValidBlock(b: Block): bool = and {
        b.block_id >= 0 and b.block_id <= 3,
        b.prev_block_id >= -1 and b.prev_block_id <= 3
    }

    // Ação para verificar todas as condições de tipo
    action POWTypeOK = all {
        // Verifica se todos os elementos de blcks seguem o tipo Block
        blcks.forall(isValidBlock),

        // Verifica se chain é um mapeamento de nodes para subconjuntos de Block
        nodes.forall(n => chain.get(n).subseteq(blcks)),

        // Verifica se last_block_id é um mapeamento de nodes para valores entre 0 e 3
        nodes.forall(n => last_block_id.get(n) >= 0 and last_block_id.get(n) <= 3),

        // Verifica se status é um mapeamento de nodes para MINED ou MINER
        nodes.forall(n => Set(MINED, MINER).contains(status.get(n))),

        // Verifica se status_changer é um mapeamento de nodes para 0 ou 1
        nodes.forall(n => Set(0, 1).contains(status_changer.get(n)))
    }
}
